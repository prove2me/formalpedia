-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_hd_invT
-- name    : PI.UnitaryGroupMassFormula.UsCost.DA.hd_invT
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:12.889708+00:00
-- url     : https://prove2.me/theorems/590d3120-0bf9-4ee0-8c16-a6f0a7fc15a2
-- title:
--   DA: hd inv T
-- statement:
--   The DA construction uses the hd inv T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L136-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L136-L158

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

theorem PI.UnitaryGroupMassFormula.UsCost.DA.hd_invT {a : ℕ} (B : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) (-Bᴴ) 0 := by sorry
