-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_dLR_comp
-- name    : PI.UnitaryGroupMassFormula.UsCost.dLR_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:38.982046+00:00
-- url     : https://prove2.me/theorems/410cf959-2b5d-4df8-87ff-46f9c92aecc1
-- title:
--   Us Cost: d LR comp
-- statement:
--   The Us Cost construction uses the d LR comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L108-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L108-L119

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ} {ξ : Xi k p s ρ σ} {Z : G.Mat s}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.UnitaryGroupMassFormula.UsCost.dLR_comp (hL : SliceLeft) (hR : SliceRight) (v : List (B.Mat k ρ)) (F : B.Mat k (p + s + ρ) → E) :
    ∀ u : List (B.Mat k ρ),
      B.dLR u v (fun γ' => F (gaXi k ρ σ d ξ Z γ')) =
        fun γ' => B.dLR (u.map (cj k (p + s) ρ ξ.1.1)) (v.map (cj k (p + s) ρ ξ.1.2)) F (gaXi k ρ σ d ξ Z γ')
  := by sorry
