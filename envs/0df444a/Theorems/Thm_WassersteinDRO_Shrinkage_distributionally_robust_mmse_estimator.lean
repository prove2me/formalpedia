-- Prove2me | Theorems.Thm_WassersteinDRO_Shrinkage_distributionally_robust_mmse_estimator
-- name    : WassersteinDRO.Shrinkage.distributionally_robust_mmse_estimator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T02:52:33.23903+00:00
-- url     : https://prove2.me/theorems/0045abcc-74c8-4c06-ae4c-d81420ef788b
-- title:
--   Theorem 25 — Distributionally robust MMSE estimator
-- statement:
--   If $\hat\Sigma \succ 0$, then the estimation problem (35) is equivalent to the nonlinear
--   convex SDP (36): its optimal value equals the SDP's optimal value. Moreover, if $S^\star$ is
--   optimal in (36) with $S^\star_{yy}$ invertible, then the affine function $\psi^\star(y) =
--   S^\star_{xy}(S^\star_{yy})^{-1}(y-\hat\mu_y)+\hat\mu_x$ attains the outer infimum of (35),
--   i.e. is a distributionally robust MMSE estimator.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Theorem 25, p. 29

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_IsElliptical
import Definitions.Def_WassersteinDRO_Shrinkage_robustMMSEValue
import Definitions.Def_WassersteinDRO_Shrinkage_sdpValue
import Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet
import Definitions.Def_WassersteinDRO_Shrinkage_sdpObjective
import Definitions.Def_WassersteinDRO_Shrinkage_estimationLoss
import Definitions.Def_WassersteinDRO_Shrinkage_ambiguitySet
import Definitions.Def_WassersteinDRO_Shrinkage_nominalRisk
import Definitions.Def_WassersteinDRO_Shrinkage_affineEstimator

open MeasureTheory

namespace WassersteinDRO.Shrinkage

/-- Theorem 25 (Distributionally robust MMSE estimator), Kuhn et al. 2019, p. 29 — the goal
theorem: if `Σ̂ ≻ 0`, then the estimation problem (35) is equivalent to the nonlinear convex
SDP (36) — `robustMMSEValue ε PN = sdpValue ε Σ̂ λmin`, `λmin` the least eigenvalue of `Σ̂` —
and if `S⋆` is optimal in (36) with `S⋆_yy` invertible (an added hypothesis not explicit on the
page; see `MODERATION_NOTES.md`, pitfall 5), then the affine function
`ψ⋆(y) = S⋆_xy(S⋆_yy)⁻¹(y-µ̂_y) + µ̂_x` attains the outer infimum of (35), i.e. is a
distributionally robust MMSE estimator. -/
theorem distributionally_robust_mmse_estimator {mx my : ℕ}
    (ε : ℝ) (hε : 0 < ε)
    (SigmaHat : Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ)
    (hSigmaHatSymm : SigmaHat.IsHermitian) (hSigmaHatPD : SigmaHat.PosDef)
    (lambdaMin : ℝ) (hLambdaMinLB : ∀ i, lambdaMin ≤ hSigmaHatSymm.eigenvalues i)
    (hLambdaMinAttained : ∃ i, lambdaMin = hSigmaHatSymm.eigenvalues i)
    (muHatX : EuclideanSpace ℝ (Fin mx)) (muHatY : EuclideanSpace ℝ (Fin my))
    (muHat : EuclideanSpace ℝ (Fin mx ⊕ Fin my))
    (hmuHatX : ∀ i : Fin mx, muHat (Sum.inl i) = muHatX i)
    (hmuHatY : ∀ i : Fin my, muHat (Sum.inr i) = muHatY i)
    (g : ℝ → ℝ) (PN : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my)))
    (hElliptical : IsElliptical PN g muHat SigmaHat) :
    robustMMSEValue ε PN = sdpValue ε SigmaHat lambdaMin ∧
      ∀ S : Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ,
        S ∈ sdpFeasibleSet ε SigmaHat lambdaMin →
        (sdpObjective S : EReal) = sdpValue ε SigmaHat lambdaMin →
        S.toBlocks₂₂.PosDef →
        ⨆ (Q : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my)))
            (_ : Q ∈ ambiguitySet ε 2 Set.univ PN)
            (_ : Integrable
              (estimationLoss (affineEstimator S.toBlocks₁₂ S.toBlocks₂₂ muHatX muHatY)) Q),
          (nominalRisk Q
              (estimationLoss (affineEstimator S.toBlocks₁₂ S.toBlocks₂₂ muHatX muHatY)) :
              EReal) =
          robustMMSEValue ε PN := by sorry

end WassersteinDRO.Shrinkage
