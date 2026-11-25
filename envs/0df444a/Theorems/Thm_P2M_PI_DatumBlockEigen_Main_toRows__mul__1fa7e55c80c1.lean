-- Prove2me | Theorems.Thm_P2M_PI_DatumBlockEigen_Main_toRows__mul__1fa7e55c80c1
-- name    : P2M_PI_DatumBlockEigen_Main_toRows__mul__1fa7e55c80c1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:55:41.888408+00:00
-- url     : https://prove2.me/theorems/649bd021-92ba-5167-897e-f60afc0b4a71
-- title:
--   P2 M PI Datum Block Eigen Main to Rows  mul  1fa7e55c80c1: P2 M PI Datum Block Eigen Main to Rows  mul  1fa7e55c80c1
-- statement:
--   The P2 M PI Datum Block Eigen Main to Rows  mul  1fa7e55c80c1 construction uses the P2 M PI Datum Block Eigen Main to Rows  mul  1fa7e55c80c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L18-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Main
open PI.DatumBlockEigen.Unit Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}

theorem P2M_PI_DatumBlockEigen_Main_toRows__mul__1fa7e55c80c1 (N : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F)
    (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) :
    toRows₁ (N * x) = N.toBlocks₁₁ * toRows₁ x + N.toBlocks₁₂ * toRows₂ x := by sorry

alias «PI».«DatumBlockEigen».«Main».«toRows₁_mul'» := P2M_PI_DatumBlockEigen_Main_toRows__mul__1fa7e55c80c1
