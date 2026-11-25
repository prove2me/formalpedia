-- Prove2me | Theorems.Thm_P2M_PI_Landherr__unitNormLoc_add_lt_ceb1586227f0
-- name    : P2M_PI_Landherr__unitNormLoc_add_lt_ceb1586227f0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:15.675595+00:00
-- url     : https://prove2.me/theorems/482187b0-e2da-52f8-bbfd-a52a062249a7
-- title:
--   P2 M PI Landherr  unit Norm Loc add lt ceb1586227f0: P2 M PI Landherr  unit Norm Loc add lt ceb1586227f0
-- statement:
--   The P2 M PI Landherr  unit Norm Loc add lt ceb1586227f0 construction uses the P2 M PI Landherr  unit Norm Loc add lt ceb1586227f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LandherrUnitNorm/UnitNormLoc.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LandherrUnitNorm/UnitNormLoc.lean#L18-L19

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

theorem P2M_PI_Landherr__unitNormLoc_add_lt_ceb1586227f0 {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} {r : ℝ}
    (hx : ‖x‖ < r) (hy : ‖y‖ < r) : ‖x + y‖ < r := by sorry

alias «PI».«Landherr₃».«unitNormLoc_add_lt» := P2M_PI_Landherr__unitNormLoc_add_lt_ceb1586227f0
