-- Prove2me | Theorems.Thm_PI_BiaddOfCubeWork_simeq_of_sub_eq
-- name    : PI.BiaddOfCubeWork.simeq_of_sub_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:32.88667+00:00
-- url     : https://prove2.me/theorems/29878a8d-4565-421a-9d02-aa1da5db1550
-- title:
--   Biadd Of Cube Work: simeq of sub eq
-- statement:
--   The Biadd Of Cube Work construction uses the simeq of sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditiveCubes/ConstantCoeffLogEqZero.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditiveCubes/ConstantCoeffLogEqZero.lean#L63-L67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BiaddOfCube
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BiaddOfCubeWork
open PI.BiaddOfCube
variable {p : ℕ} [Fact p.Prime]
variable {σ : Type*}

theorem PI.BiaddOfCubeWork.simeq_of_sub_eq {f g f' g' : MvPowerSeries σ ℂ_[p]} (e : f - g = f' - g')
    (hs : Simeq f' g') : Simeq f g := by sorry
