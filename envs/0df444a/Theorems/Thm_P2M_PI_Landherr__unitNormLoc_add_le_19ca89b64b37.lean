-- Prove2me | Theorems.Thm_P2M_PI_Landherr__unitNormLoc_add_le_19ca89b64b37
-- name    : P2M_PI_Landherr__unitNormLoc_add_le_19ca89b64b37
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:52:35.177044+00:00
-- url     : https://prove2.me/theorems/d89dbad7-e1d3-59d1-b136-7759b1e8a0b4
-- title:
--   P2 M PI Landherr  unit Norm Loc add le 19ca89b64b37: P2 M PI Landherr  unit Norm Loc add le 19ca89b64b37
-- statement:
--   The P2 M PI Landherr  unit Norm Loc add le 19ca89b64b37 construction uses the P2 M PI Landherr  unit Norm Loc add le 19ca89b64b37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LandherrUnitNorm/UnitNormLoc.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LandherrUnitNorm/UnitNormLoc.lean#L21-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LandherrUnitNorm_UnitNormLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open PI PI.Landherr₃

theorem P2M_PI_Landherr__unitNormLoc_add_le_19ca89b64b37 {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} {r : ℝ}
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r := by sorry

alias «PI».«Landherr₃».«unitNormLoc_add_le» := P2M_PI_Landherr__unitNormLoc_add_le_19ca89b64b37
