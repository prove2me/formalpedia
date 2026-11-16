-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_Supplement_lemma_B_2
-- name    : ParallelDiffusionLB.NearIsotropic.Supplement.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:09:44.987808+00:00
-- url     : https://prove2.me/theorems/609199ed-f92e-4c3a-a1c4-50ed3954e6e6
-- title:
--   Lemma B.2 — Accuracy of the gated oracle
-- statement:
--   Let $a,b\in\mathbb N$. For all sufficiently large $d$, every query budget $1\le P\le d^a$ and every score accuracy $d^{-b}\le\varepsilon\le1$, the following holds for every instance $\theta\in[M]^d$ of the box family (53)–(54), with target $\pi^\theta=\mathrm{Unif}(K^\theta)$ and gated oracle $\hat s^\theta$ of (57).
--
--   1. For every noise level $\sigma>0$,
--   $$\mathbb E_{X\sim(\pi^\theta)^{(\sigma)}}\bigl\|\hat s^\theta_\sigma(X)-s_{\pi^\theta,\sigma}(X)\bigr\|_2^2\le\frac{\varepsilon^2}{2\sigma^2},\qquad(58)$$
--   where $(\pi^\theta)^{(\sigma)}$ is the law of $Y+\sigma Z$, $Y\sim\pi^\theta$, $Z\sim N(0,I_d)$ independent, and $s_{\pi^\theta,\sigma}=\nabla\log$ of its density.
--   2. In particular $\hat s^\theta$ is a legal score oracle for $\pi^\theta$ at accuracy $\varepsilon$: it is a jointly measurable map of $(x,\sigma)$ and its mean squared error at every $\sigma>0$ is at most $\varepsilon^2/\sigma^2$.
--
--   This supplies the legal oracles of Theorem 4.1; the constant $1/2$ in (58) is stronger than legality.
--
--   **Formalization Note** The expectation is the extended nonnegative integral `squaredError`, so a non-integrable error cannot make the bound hold by default.
--
--   Differences from the source:
--   - encoding: for sufficiently large d, with a polynomial budget P = poly(d) and an inverse-polynomial accuracy ε_score = poly(d)^{-1} fixed beforehand → ∀ a b : ℕ, ∃ d₀, ∀ d ≥ d₀, ∀ P with 1 ≤ P ≤ d^a, ∀ ε > 0 with d^{-b} ≤ ε; reason: every polynomial budget is eventually at most d^a and every inverse polynomial eventually at least d^{-b}, for some a, b; this is the shape of the published theorem_3_1
--   - reading: ε_score = poly(d)^{-1} (inverse-polynomial accuracy) → ε ≤ 1; reason: an inverse polynomial accuracy is at most 1 for large d; some upper bound is needed (for ε > 100Md, q < 1 and the boxes leave the unit ball), and ε ≤ 1 is the natural one; the proof on pp. 31–32 uses only q ≥ 2, i.e. ε ≤ 50Md, which ε ≤ 1 implies
--   - encoding: coordinates i ∈ [d] and labels k ∈ [M], 1-indexed → i : Fin d and k : Fin M, 0-indexed (paper i = i.val + 1, paper k = k.val + 1); reason: Lean convention; same objects
--   - encoding: E_{X∼(π^θ)^{(σ)}} ‖ŝ^θ_σ(X) − s^θ_σ(X)‖² ≤ ε²/(2σ²) → the published squaredError (an ℝ≥0∞-valued lintegral under smoothLaw (Unif K^θ) σ) is at most ENNReal.ofReal (ε²/(2σ²)); reason: the nonnegative integral cannot default to 0 on a non-integrable error
--   - encoding: true score s^θ_σ = ∇ log of the density of (π^θ)^{(σ)} → the published score of Unif(K^θ) at σ, built from the everywhere-defined convolution density; reason: the published definition of §2.1
--   - encoding: the oracle is fixed before interaction → no separate conjunct; reason: the Lean oracle is a function of θ alone
--   - encoding: legal at score accuracy ε_score → LegalOracle (Unif K^θ) ε (gatedOracle θ), which includes joint measurability in (x, σ); reason: the published definition of (1)
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma B.2, p. 31 (oracle (57), p. 31; proof pp. 31–32)

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Supplement_Box

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic.Supplement

/-- Lemma B.2 (Complete version of Lemma 4.2), p. 31, in the regime of B.1/(53).
For every instance `θ`, the gated oracle (57) satisfies (58) with the constant `1/2` at every
`σ > 0`, the error being the extended nonnegative integral of `‖ŝ^θ_σ - s^θ_σ‖²` under the
noisy target `(π^θ)^{(σ)}`, `π^θ = Unif(K^θ)`; and it is a legal oracle at accuracy `ε`
(which includes joint measurability in `(x, σ)`). -/
theorem lemma_B_2 (a b : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ P : ℕ, 1 ≤ P → P ≤ d ^ a →
    ∀ ε : ℝ, 0 < ε → (d : ℝ) ^ (-(b : ℤ)) ≤ ε → ε ≤ 1 →
    ∀ θ : Fin d → Fin (numIntervals d P),
      (∀ σ : {σ : ℝ // 0 < σ},
        squaredError (smoothLaw (unifSet (box d P ε θ)) σ.1)
            (fun x => gatedOracle d P ε θ (x, σ)) (score (unifSet (box d P ε θ)) σ.1) ≤
          ENNReal.ofReal (ε ^ 2 / (2 * σ.1 ^ 2))) ∧
      LegalOracle (unifSet (box d P ε θ)) ε (gatedOracle d P ε θ) := by sorry

end ParallelDiffusionLB.NearIsotropic.Supplement
