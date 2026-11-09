-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_7
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:53.220303+00:00
-- url     : https://prove2.me/theorems/f3069020-16c0-4775-a0aa-1e7dcd13616b
-- title:
--   Lemma A.7 — Accuracy of the gated oracle
-- statement:
--   Fix $1\le B\le d$, $m=\lfloor d/B\rfloor\ge\max\{2,\sqrt2\gamma\}$, $\gamma>0$, $0<\varepsilon\le1$, $0<\rho\le1/10$, and arbitrary fixed nonempty codebooks. Use the product oracle (30), the one-block gate and local answer, and the exact public padding score. For every $\tau\ge\gamma$,
--   $$E_{\pi_\tau^S}\|\hat s_\tau^S-s_\tau^S\|^2\le\frac{B(B+1)\eta^2}{8\tau^2}\le\frac{\varepsilon^2}{256\tau^2}.$$
--   Consequently $\hat s^S(x,\sigma)=\hat s_{\sqrt{\gamma^2+\sigma^2}}^S(x)$ is a fixed legal score oracle for $\pi^S$, jointly measurable, and accurate at every $\sigma>0$. This includes the quantitative bound before the legality conclusion.
--
--   Differences from the source:
--   - encoding: d coordinates in B consecutive blocks and d−Bm padding coordinates, m=⌊d/B⌋ → Layout with d=B*m+pad and an explicit hypothesis m=d/B when the source uses that convention; reason: this labels the same coordinates; padding may be zero and the empty product is one
--   - encoding: nonempty subsets of {−1,+1}^m → finite sets of Boolean-labelled cube vertices with nonemptiness or positive prescribed cardinality; reason: the vertex map is a bijection and the uniform subset law samples without replacement
--   - encoding: nonnegative expectations and KL divergence → nonnegative Lebesgue integrals and Mathlib KL divergence valued in [0,∞]; reason: all values for the stated Gaussian mixtures are finite and the inequalities are unchanged; a divergent error cannot default to zero
--   - generalization: the fixed constructed oracle satisfies (1) → the same oracle also has joint measurability in location and noise; reason: the explicit finite-mixture construction is measurable and the additional property ensures all randomized output laws are defined
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.7, p. 23

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

theorem lemma_A_7 (L : Layout) (hfloor : L.m = L.d / L.B)
    (γ ε ρ : ℝ) (hγ : 0 < γ) (hm : 2 ≤ L.m) (hmg : Real.sqrt 2 * γ ≤ L.m)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/10)
    (S : L.Books) (hS : L.booksValid S) :
    (∀ τ : ℝ, γ ≤ τ →
      squaredError (L.targetLaw S τ) (L.totalOracle ε ρ τ S) (score (L.centerLaw S) τ) ≤
        ENNReal.ofReal (L.B * (L.B + 1) * localBudget L.B ε ^ 2 / (8 * τ ^ 2)) ∧
      (L.B : ℝ) * (L.B + 1) * localBudget L.B ε ^ 2 / (8 * τ ^ 2) ≤ ε ^ 2 / (256 * τ ^ 2)) ∧
    LegalOracle (L.targetLaw S γ) ε (L.oracle γ ε ρ S) := by sorry

end ParallelDiffusionLB.NearIsotropic
