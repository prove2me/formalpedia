-- Prove2me | Theorems.Thm_SchattenSketch_Main_lemma_4_1
-- name    : SchattenSketch.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:29.282257+00:00
-- url     : https://prove2.me/theorems/8824fb8f-566c-40d7-9113-67a3e208e00f
-- title:
--   Lemma 4.1 — Yao–Le Cam reduction: separated values and small total variation after every rank-$\le k$ coisometry rule out every valid $k$-dimensional sketch
-- statement:
--   Let $\Phi:\mathbb R^{n\times n}\to[0,\infty)$ be measurable and let $\Pi_0,\Pi_1$ be probability laws on $\mathbb R^{n\times n}$, with $A_i\sim\Pi_i$. Suppose there are deterministic measurable sets $I_0,I_1\subseteq[0,\infty)$ and reals $\varepsilon,\zeta,\delta$ such that $P\{\Phi(A_i)\in I_i\}\ge 1-\zeta$ for $i=0,1$, the enlargements $(1\pm\varepsilon)I_0$ and $(1\pm\varepsilon)I_1$ are disjoint, and for every row coisometry $L$ of rank $r\le k$
--   $$d_{TV}(L_\#\Pi_0,\,L_\#\Pi_1)\le\delta,\qquad \delta+2\zeta<\tfrac13 .$$
--   Then no randomized $k$-dimensional linear sketch $(S_\omega,d_\omega)$ satisfies $P_\omega\{(1-\varepsilon)\Phi(A)\le d_\omega(S_\omega A)\le(1+\varepsilon)\Phi(A)\}\ge 2/3$ for every fixed $A$.
--
--   This is the reduction from estimation to binary testing that turns the two hard input laws of §4 into the lower half of Theorem 1.1.
--
--   **Formalization Note.** Laws on matrices live on arrays `Fin n → Fin n → ℝ` (Mathlib has no σ-algebra on `Matrix`); $\Phi$ is a function on matrices whose composition with `Matrix.of` is measurable. $I_0,I_1$ are measurable, so $P\{\Phi(A_i)\in I_i\}$ is the probability of an event. The sketch class is `LinearSketch n k` and validity is `IsValid`.
--
--   Differences from the source:
--   - reading: a distribution of linear maps S_ω and measurable decoders d_ω (p. 4) → LinearSketch: seed space Ω : Type with a probability measure, S measurable in ω, decoder jointly measurable in (ω, y); reason: the paper's measurable decoders, with the joint measurability its Yao averaging (p. 35) and its measurable SVD convention (p. 31) use
--   - encoding: probability laws Π_0, Π_1 on R^{n×n}, Φ measurable → measures on arrays Fin n → Fin n → ℝ; A ↦ Φ (Matrix.of A) measurable; reason: Mathlib has no σ-algebra on Matrix; the same space
--   - encoding: P{Φ(A_i) ∈ I_i} ≥ 1 − ζ → ENNReal.ofReal (1 − ζ) ≤ Π_i {A | Φ (Matrix.of A) ∈ I_i}; reason: probabilities in ℝ≥0∞; the same inequality
--   - encoding: every rank-at-most-k row coisometry L → every r ≤ k and every L : Fin r → Fin n × Fin n → ℝ with L Lᵀ = I_r; reason: a row coisometry of rank r has exactly r orthonormal rows
--   - reading: deterministic sets I_0, I_1 ⊆ [0, ∞) with P{Φ(A_i) ∈ I_i} ≥ 1 − ζ → MeasurableSet I_0, MeasurableSet I_1; reason: P{Φ(A_i) ∈ I_i} is the probability of an event, so the page presupposes it measurable; without it the statement is false at ε = 0 (a Bernstein set and its complement in [1, 2], each of full outer measure, are disjoint (1 ± 0)-enlargements while Φ itself is a valid sketch)
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 14, Lemma 4.1 (proof p. 35, A.1)

import Mathlib
import Definitions.Def_SchattenSketch_Main_Sketch
import Definitions.Def_SchattenSketch_Main_Testing

open MeasureTheory

namespace SchattenSketch.Main

/-- Lemma 4.1 (Yao–Le Cam reduction; Yang, p. 14). Input laws `Π₀, Π₁` on `ℝ^{n×n}` (as arrays
`Fin n → Fin n → ℝ`), a measurable nonnegative functional `Φ`, measurable sets `I₀, I₁ ⊆ [0, ∞)` with
`P{Φ(Aᵢ) ∈ Iᵢ} ≥ 1 - ζ` and disjoint enlargements, and total variation at most `δ` after every
row coisometry of rank at most `k`, with `δ + 2ζ < 1/3`: then no randomized `k`-dimensional
linear sketch is `(1 ± ε)`-valid for `Φ`. -/
theorem lemma_4_1 (n k : ℕ) (Φ : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hΦ : Measurable fun A : Fin n → Fin n → ℝ => Φ (Matrix.of A))
    (hΦ_nonneg : ∀ A, 0 ≤ Φ A)
    (μ₀ μ₁ : Measure (Fin n → Fin n → ℝ)) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (I₀ I₁ : Set ℝ) (hI₀m : MeasurableSet I₀) (hI₁m : MeasurableSet I₁)
    (hI₀ : I₀ ⊆ Set.Ici 0) (hI₁ : I₁ ⊆ Set.Ici 0) (ε ζ δ : ℝ)
    (hμ₀ : ENNReal.ofReal (1 - ζ) ≤ μ₀ {A | Φ (Matrix.of A) ∈ I₀})
    (hμ₁ : ENNReal.ofReal (1 - ζ) ≤ μ₁ {A | Φ (Matrix.of A) ∈ I₁})
    (hdisj : Disjoint (enlarge ε I₀) (enlarge ε I₁))
    (hTV : ∀ r : ℕ, r ≤ k → ∀ L : Fin r → Fin n × Fin n → ℝ, IsRowCoisometry L →
      tvDist (μ₀.map fun A => sketchApply L (Matrix.of A))
        (μ₁.map fun A => sketchApply L (Matrix.of A)) ≤ δ)
    (hδζ : δ + 2 * ζ < 1 / 3) :
    ∀ sk : LinearSketch n k, ¬ sk.IsValid Φ ε := by sorry

end SchattenSketch.Main
