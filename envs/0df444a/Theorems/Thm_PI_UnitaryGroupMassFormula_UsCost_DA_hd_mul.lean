-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_hd_mul
-- name    : PI.UnitaryGroupMassFormula.UsCost.DA.hd_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:50:57.254792+00:00
-- url     : https://prove2.me/theorems/47baca51-408a-45ce-bf15-7756d2545b76
-- title:
--   DA: hd mul
-- statement:
--   The DA construction uses the hd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L103-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L103-L110

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

theorem PI.UnitaryGroupMassFormula.UsCost.DA.hd_mul {a b c : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {G : ℝ → Matrix (Fin b) (Fin c) ℂ}
    {F' : Matrix (Fin a) (Fin b) ℂ} {G' : Matrix (Fin b) (Fin c) ℂ}
    (hF : HasDerivAt F F' t) (hG : HasDerivAt G G' t) :
    HasDerivAt (fun y => F y * G y) (F' * G t + F t * G') t := by sorry
