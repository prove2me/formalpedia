-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_Supplement_lemma_B_1
-- name    : ParallelDiffusionLB.NearIsotropic.Supplement.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:09:11.276831+00:00
-- url     : https://prove2.me/theorems/b96876a7-6b69-44c6-bedb-9a68c707c95b
-- title:
--   Lemma B.1 — Geometry and gates
-- statement:
--   Let $a,b\in\mathbb N$. For all sufficiently large $d$, every query budget $1\le P\le d^a$ and every score accuracy $d^{-b}\le\varepsilon\le1$, the public parameters (53)–(54) $M,q,a_i,h_i,t_i,c_i(k),I_i(k)$ and the gates (55) have the following properties.
--
--   1. Every box $K^\theta=\prod_{i}I_i(\theta_i)$, $\theta\in[M]^d$, is full-dimensional (it has nonempty interior) and is contained in the open unit ball $B_2(0,1)$.
--   2. Every interval $I_i(k)$ lies in $[a_i,2a_i]$.
--   3. For each $i$, the intervals $I_i(1),\dots,I_i(M)$ are pairwise disjoint.
--   4. Consecutive centers are spaced by $c_i(k+1)-c_i(k)=a_i/M$, and $a_i/M=100h_i$.
--   5. For $i<d$ and $0<\sigma\le t_{i+1}$, the sets $\{z\in\mathbb R:g^k_{i,\sigma}(z)>0\}$, $k\in[M]$, are pairwise disjoint.
--   6. For $i<d$, $k\in[M]$, every $\sigma>0$, and independent $U_i\sim\mathrm{Unif}(I_i(k))$, $Z_i\sim N(0,1)$,
--   $$\Pr\bigl[g^k_{i,\sigma}(U_i+\sigma Z_i)<1\bigr]\le2\exp\Bigl(-\frac{50h_i^2}{\sigma^2}\Bigr).\qquad(56)$$
--
--   These geometric facts give the boxes of Theorem 4.1 their required shape and supply the gate estimates used for the accuracy of the gated oracle (Lemma B.2) and for the one-coordinate-per-round simulation (Lemma B.3).
--
--   **Formalization Note** Coordinates and labels are 0-indexed, so "$i<d$" is `i.val + 1 < d` and $t_{i+1}$ is the cutoff of coordinate `⟨i.val + 1, _⟩`.
--
--   Differences from the source:
--   - encoding: for sufficiently large d, with a polynomial budget P = poly(d) and an inverse-polynomial accuracy ε_score = poly(d)^{-1} fixed beforehand → ∀ a b : ℕ, ∃ d₀, ∀ d ≥ d₀, ∀ P with 1 ≤ P ≤ d^a, ∀ ε > 0 with d^{-b} ≤ ε; reason: every polynomial budget is eventually at most d^a and every inverse polynomial eventually at least d^{-b}, for some a, b; this is the shape of the published theorem_3_1
--   - reading: ε_score = poly(d)^{-1} (inverse-polynomial accuracy) → ε ≤ 1; reason: an inverse polynomial accuracy is at most 1 for large d; some upper bound is needed (for ε > 100Md, q < 1 and the boxes leave the unit ball), and ε ≤ 1 is the natural one; the proof on pp. 31–32 uses only q ≥ 2, i.e. ε ≤ 50Md, which ε ≤ 1 implies
--   - encoding: coordinates i ∈ [d] and labels k ∈ [M], 1-indexed → i : Fin d and k : Fin M, 0-indexed (paper i = i.val + 1, paper k = k.val + 1); reason: Lean convention; same objects
--   - encoding: K^θ is full-dimensional → the interior of K^θ in E d is nonempty; reason: the standard meaning of full-dimensional; the paper's proof gives it from the positive lengths
--   - reading: contained in B_2(0, 1) → contained in the open ball Metric.ball 0 1; reason: B_2(0,1) does not say open or closed; the open ball is the stronger reading and the proof gives ‖x‖² ≤ 1/3
--   - encoding: center spacing a_i/M = 100h_i → consecutive centers differ by a_i/M, and a_i/M = 100 h_i; reason: spacing of equally spaced centers is the difference of consecutive ones
--   - encoding: Pr over independent U_i ∼ Unif(I_i(k)) and Z_i ∼ N(0,1) → the real measure of the event under the product of the uniform law of I_i(k) and gaussianReal 0 1; reason: independence is the product measure
--   - encoding: g^k_{i,σ} defined only for i < d → gate with placeholder value 1 at the last coordinate, all gate clauses quantified over i with i.val + 1 < d; reason: the placeholder is never used
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma B.1, p. 31 (parameters (53)–(55), pp. 30–31)

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Supplement_Box

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic.Supplement

/-- Lemma B.1 (Geometry and gates), p. 31, in the regime of B.1/(53): polynomial query budget
`1 ≤ P ≤ d^a`, inverse-polynomial accuracy `d^{-b} ≤ ε ≤ 1`, all sufficiently large `d`.
Indices are 0-indexed: the paper's `i < d` is `i.val + 1 < d` and `t_{i+1}` is the cutoff of
coordinate `⟨i.val + 1, _⟩`. -/
theorem lemma_B_1 (a b : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ P : ℕ, 1 ≤ P → P ≤ d ^ a →
    ∀ ε : ℝ, 0 < ε → (d : ℝ) ^ (-(b : ℤ)) ≤ ε → ε ≤ 1 →
      -- every box is full-dimensional and lies in the open unit ball
      (∀ θ : Fin d → Fin (numIntervals d P),
        (interior (box d P ε θ)).Nonempty ∧ box d P ε θ ⊆ Metric.ball (0 : E d) 1) ∧
      -- the candidate intervals lie in `[a_i, 2 a_i]`
      (∀ (j : Fin d) (k : Fin (numIntervals d P)),
        interval d P ε j k ⊆ Set.Icc (scale d P ε j) (2 * scale d P ε j)) ∧
      -- and are pairwise disjoint
      (∀ (j : Fin d) (k k' : Fin (numIntervals d P)), k ≠ k' →
        Disjoint (interval d P ε j k) (interval d P ε j k')) ∧
      -- with center spacing `a_i / M = 100 h_i`
      (∀ (j : Fin d) (k k' : Fin (numIntervals d P)), k'.val = k.val + 1 →
        center d P ε j k' - center d P ε j k = scale d P ε j / numIntervals d P) ∧
      (∀ j : Fin d, scale d P ε j / numIntervals d P = 100 * halfLen d P ε j) ∧
      -- part 1: at low noise the gate supports are pairwise disjoint
      (∀ (i : Fin d) (hi : i.val + 1 < d) (σ : ℝ), 0 < σ →
        σ ≤ cutoff d P ε ⟨i.val + 1, hi⟩ →
        ∀ k k' : Fin (numIntervals d P), k ≠ k' →
          Disjoint {z : ℝ | 0 < gate d P ε i k σ z} {z : ℝ | 0 < gate d P ε i k' σ z}) ∧
      -- part 2: the gate-failure bound (56), at every noise level
      (∀ (i : Fin d), i.val + 1 < d → ∀ (k : Fin (numIntervals d P)) (σ : ℝ), 0 < σ →
        ((unifSet (interval d P ε i k)).prod (gaussianReal 0 1)).real
            {p : ℝ × ℝ | gate d P ε i k σ (p.1 + σ * p.2) < 1} ≤
          2 * Real.exp (-(50 * halfLen d P ε i ^ 2) / σ ^ 2)) := by sorry

end ParallelDiffusionLB.NearIsotropic.Supplement
