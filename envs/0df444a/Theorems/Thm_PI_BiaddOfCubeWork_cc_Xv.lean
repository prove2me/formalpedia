-- Prove2me | Theorems.Thm_PI_BiaddOfCubeWork_cc_Xv
-- name    : PI.BiaddOfCubeWork.cc_Xv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:54.788735+00:00
-- url     : https://prove2.me/theorems/c5a01d55-fe15-455e-ad4c-7cf5d7308ce1
-- title:
--   Biadd Of Cube Work: cc Xv
-- statement:
--   The Biadd Of Cube Work construction uses the cc Xv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditiveCubes/ConstantCoeffLogEqZero.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditiveCubes/ConstantCoeffLogEqZero.lean#L69-L70

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

theorem PI.BiaddOfCubeWork.cc_Xv (i : Fin 3) : MvPowerSeries.constantCoeff (Xv (p := p) i) = 0 := by sorry
