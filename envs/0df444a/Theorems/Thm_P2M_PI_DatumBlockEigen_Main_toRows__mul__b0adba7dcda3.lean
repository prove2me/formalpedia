-- Prove2me | Theorems.Thm_P2M_PI_DatumBlockEigen_Main_toRows__mul__b0adba7dcda3
-- name    : P2M_PI_DatumBlockEigen_Main_toRows__mul__b0adba7dcda3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:55:59.797029+00:00
-- url     : https://prove2.me/theorems/852bf76c-306b-44d8-b94f-0d626e02c62f
-- title:
--   P2 M PI Datum Block Eigen Main to Rows  mul  b0adba7dcda3: P2 M PI Datum Block Eigen Main to Rows  mul  b0adba7dcda3
-- statement:
--   The P2 M PI Datum Block Eigen Main to Rows  mul  b0adba7dcda3 construction uses the P2 M PI Datum Block Eigen Main to Rows  mul  b0adba7dcda3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L25-L30

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

theorem P2M_PI_DatumBlockEigen_Main_toRows__mul__b0adba7dcda3 (N : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F)
    (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) :
    toRows₂ (N * x) = N.toBlocks₂₁ * toRows₁ x + N.toBlocks₂₂ * toRows₂ x := by sorry

alias «PI».«DatumBlockEigen».«Main».«toRows₂_mul'» := P2M_PI_DatumBlockEigen_Main_toRows__mul__b0adba7dcda3
