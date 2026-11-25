-- Prove2me | Theorems.Thm_P2M_PI_Landherr__unitNormLoc_mul_lt_575669e40379
-- name    : P2M_PI_Landherr__unitNormLoc_mul_lt_575669e40379
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:30.866854+00:00
-- url     : https://prove2.me/theorems/84a3650c-bb1a-505e-a8dc-c7833fe87e06
-- title:
--   P2 M PI Landherr  unit Norm Loc mul lt 575669e40379: P2 M PI Landherr  unit Norm Loc mul lt 575669e40379
-- statement:
--   The P2 M PI Landherr  unit Norm Loc mul lt 575669e40379 construction uses the P2 M PI Landherr  unit Norm Loc mul lt 575669e40379 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LandherrUnitNorm/UnitNormLoc.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LandherrUnitNorm/UnitNormLoc.lean#L24-L27

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

theorem P2M_PI_Landherr__unitNormLoc_mul_lt_575669e40379 {K : Type} [NormedField K] {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) :
    ‖x * y‖ < 1 := by sorry

alias «PI».«Landherr₃».«unitNormLoc_mul_lt» := P2M_PI_Landherr__unitNormLoc_mul_lt_575669e40379
