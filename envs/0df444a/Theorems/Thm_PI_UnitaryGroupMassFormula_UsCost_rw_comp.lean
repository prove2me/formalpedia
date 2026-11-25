-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_rw_comp
-- name    : PI.UnitaryGroupMassFormula.UsCost.rw_comp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:05.918807+00:00
-- url     : https://prove2.me/theorems/717ed2b5-a36f-5e4d-8b56-b008d2a65e05
-- title:
--   Us Cost: rw comp
-- statement:
--   The Us Cost construction uses the rw comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L96-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean#L96-L106

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

theorem PI.UnitaryGroupMassFormula.UsCost.rw_comp (hR : SliceRight) :
    ∀ (v : List (B.Mat k ρ)) (F : B.Mat k (p + s + ρ) → E),
      B.Rw v (fun γ' => F (gaXi k ρ σ d ξ Z γ')) =
        fun γ' => B.Rw (v.map (cj k (p + s) ρ ξ.1.2)) F (gaXi k ρ σ d ξ Z γ')
  := by sorry
