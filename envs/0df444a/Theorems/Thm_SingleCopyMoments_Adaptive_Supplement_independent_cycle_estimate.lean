-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_Supplement_independent_cycle_estimate
-- name    : SingleCopyMoments.Adaptive.Supplement.independent_cycle_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:39:56.978607+00:00
-- url     : https://prove2.me/theorems/edcb3f84-c0bd-4489-bd78-5fba5c79d0cc
-- title:
--   Lemma 42 — Independent-cycle second moments
-- statement:
--   Let $r\ge2$, $d\ge1$, $T\ge\ell\ge2$, $0<\alpha\le1/100$, $0\le\theta\le\pi/r$, and $\kappa\ge1$. Run any nonadaptive single-copy protocol, with a fixed rank-one refinement, on the physical Gaussian ensemble with $r$ spectral weights. Write $\widehat C_{\ell,T}$ for the raw ordered cycle and $G_\kappa$ for the good-record event. The joint law averages the latent prior, input-independent seed and all outcomes. It is a probability law, the good event is measurable, both squared integrands are integrable, and
--   $$\mathbb E_\theta|\widehat C_{\ell,T}|^2\le
--    \ell!\,2^\ell\frac{T^\ell}{d^{\ell-1}},\qquad
--   \mathbb E_\theta[\mathbf1_{G_\kappa}|\widehat C_{\ell,T}|^2]\le
--    \ell!\,2^\ell\frac{T^\ell}{d^{\ell-1}}.$$
--   This is the independent-cycle estimate supporting Theorem 4. There is no scaling restriction on $T$, and the law is not conditioned on $G_\kappa$.
--
--   Differences from the source:
--   - generalization: Section 7.5 uses r=t and kappa=2t → any r>=2 and kappa>=1 in the same physical family; reason: the Lemma 42 proof uses only fixed nonadaptive rank-one effects and the physical floor, and the general parameters specialize to r=t and kappa=2t
--   - encoding: nonadaptive rank-one refinement and original expectations → a fixed-refinement predicate, original joint law, and explicit probability, measurability and integrability conclusions; reason: the refinement preserves nonadaptivity; well-defined expectations and probabilities are conclusions, never premises
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 42, printed p. 49 (PDF p. 51); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Supplement_NonadaptiveCycles

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- Lemma 42, printed p.49 / PDF p.51: original joint experiment, both clauses. -/
theorem independent_cycle_estimate (d r T ℓ : ℕ) (hd : 0 < d) (hr : 2 ≤ r)
    (P : Protocol d) (hP : IncoherentPurity.Adaptive.IsNonadaptive P)
    (R : Refinement hd P) (hR : FixedRefinement R)
    (α θ κ : ℝ) (hα : 0 < α) (hαsmall : α ≤ 1/100)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / (r : ℝ))) (hκ : 1 ≤ κ)
    (hℓ : 2 ≤ ℓ) (hℓT : ℓ ≤ T) :
    IsProbabilityMeasure (jointLaw hd P r α θ T) ∧
    MeasurableSet (goodRecords R T κ) ∧
    Integrable (rawCycleSquare R r α θ T ℓ) (jointLaw hd P r α θ T) ∧
    Integrable (goodCycleSquare R r α θ κ T ℓ) (jointLaw hd P r α θ T) ∧
    (∫ w, rawCycleSquare R r α θ T ℓ w ∂jointLaw hd P r α θ T) ≤
      (ℓ.factorial : ℝ) * 2^ℓ * (T : ℝ)^ℓ / (d : ℝ)^(ℓ-1) ∧
    (∫ w, goodCycleSquare R r α θ κ T ℓ w ∂jointLaw hd P r α θ T) ≤
      (ℓ.factorial : ℝ) * 2^ℓ * (T : ℝ)^ℓ / (d : ℝ)^(ℓ-1) := by sorry

end SingleCopyMoments.Adaptive.Supplement
