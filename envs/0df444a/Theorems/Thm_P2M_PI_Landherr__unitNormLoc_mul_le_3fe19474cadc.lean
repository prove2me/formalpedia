-- Prove2me | Theorems.Thm_P2M_PI_Landherr__unitNormLoc_mul_le_3fe19474cadc
-- name    : P2M_PI_Landherr__unitNormLoc_mul_le_3fe19474cadc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:22.58068+00:00
-- url     : https://prove2.me/theorems/c8bc2d42-d595-5d58-a3a9-3bfab36e7401
-- title:
--   P2 M PI Landherr  unit Norm Loc mul le 3fe19474cadc: P2 M PI Landherr  unit Norm Loc mul le 3fe19474cadc
-- statement:
--   The P2 M PI Landherr  unit Norm Loc mul le 3fe19474cadc construction uses the P2 M PI Landherr  unit Norm Loc mul le 3fe19474cadc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LandherrUnitNorm/UnitNormLoc.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LandherrUnitNorm/UnitNormLoc.lean#L29-L32

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

theorem P2M_PI_Landherr__unitNormLoc_mul_le_3fe19474cadc {K : Type} [NormedField K] {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x * y‖ ≤ 1 := by sorry

alias «PI».«Landherr₃».«unitNormLoc_mul_le» := P2M_PI_Landherr__unitNormLoc_mul_le_3fe19474cadc
