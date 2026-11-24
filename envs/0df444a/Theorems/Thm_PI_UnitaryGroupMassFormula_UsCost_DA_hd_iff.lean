-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_hd_iff
-- name    : PI.UnitaryGroupMassFormula.UsCost.DA.hd_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:50:51.272375+00:00
-- url     : https://prove2.me/theorems/82080449-ad49-4a53-903d-9d4c0f038b22
-- title:
--   DA: hd iff
-- statement:
--   The DA construction uses the hd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L99-L101

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {t : ℝ}

theorem PI.UnitaryGroupMassFormula.UsCost.DA.hd_iff {a b : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {F' : Matrix (Fin a) (Fin b) ℂ} :
    HasDerivAt F F' t ↔ ∀ i j, HasDerivAt (fun y => F y i j) (F' i j) t := by sorry
