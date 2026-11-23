-- Prove2me | Theorems.Thm_P2M_PI_BiaddOfCubeWork_add_comm__d811c4cba816
-- name    : P2M_PI_BiaddOfCubeWork_add_comm__d811c4cba816
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:18.343897+00:00
-- url     : https://prove2.me/theorems/2ac858ad-20ce-4abb-8949-33d95636fb36
-- title:
--   P2 M PI Biadd Of Cube Work add comm  d811c4cba816: P2 M PI Biadd Of Cube Work add comm  d811c4cba816
-- statement:
--   The P2 M PI Biadd Of Cube Work add comm  d811c4cba816 construction uses the P2 M PI Biadd Of Cube Work add comm  d811c4cba816 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditiveCubes/ConstantCoeffLogEqZero.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditiveCubes/ConstantCoeffLogEqZero.lean#L41-L45

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

theorem P2M_PI_BiaddOfCubeWork_add_comm__d811c4cba816 (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) :
    add l ex a b = add l ex b a := by sorry

alias «PI».«BiaddOfCubeWork».«add_comm'» := P2M_PI_BiaddOfCubeWork_add_comm__d811c4cba816
