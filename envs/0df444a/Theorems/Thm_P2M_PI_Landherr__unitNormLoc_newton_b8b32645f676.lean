-- Prove2me | Theorems.Thm_P2M_PI_Landherr__unitNormLoc_newton_b8b32645f676
-- name    : P2M_PI_Landherr__unitNormLoc_newton_b8b32645f676
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:38.049805+00:00
-- url     : https://prove2.me/theorems/f7ef01fe-e20d-5704-b102-bd5124102cba
-- title:
--   P2 M PI Landherr  unit Norm Loc newton b8b32645f676: P2 M PI Landherr  unit Norm Loc newton b8b32645f676
-- statement:
--   The P2 M PI Landherr  unit Norm Loc newton b8b32645f676 construction uses the P2 M PI Landherr  unit Norm Loc newton b8b32645f676 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LandherrUnitNorm/UnitNormLoc.lean#L34-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LandherrUnitNorm/UnitNormLoc.lean#L34-L125

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

theorem P2M_PI_Landherr__unitNormLoc_newton_b8b32645f676 {K : Type} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (α β γ a : K) (hα : ‖α‖ ≤ 1) (h : ‖α * a ^ 2 + β * a + γ‖ < ‖2 * α * a + β‖ ^ 2) :
    ∃ x : K, α * x ^ 2 + β * x + γ = 0 := by sorry

alias «PI».«Landherr₃».«unitNormLoc_newton» := P2M_PI_Landherr__unitNormLoc_newton_b8b32645f676
