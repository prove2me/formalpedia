-- Prove2me | Theorems.Thm_P2M_PI_DatumBlockEigen_Main_toBlocks___mul__15850fd75cb5
-- name    : P2M_PI_DatumBlockEigen_Main_toBlocks___mul__15850fd75cb5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:04.680626+00:00
-- url     : https://prove2.me/theorems/6f7a25fa-ea0f-5993-bccf-1d0e18e47da4
-- title:
--   P2 M PI Datum Block Eigen Main to Blocks   mul  15850fd75cb5: P2 M PI Datum Block Eigen Main to Blocks   mul  15850fd75cb5
-- statement:
--   The P2 M PI Datum Block Eigen Main to Blocks   mul  15850fd75cb5 construction uses the P2 M PI Datum Block Eigen Main to Blocks   mul  15850fd75cb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L38-L42

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

theorem P2M_PI_DatumBlockEigen_Main_toBlocks___mul__15850fd75cb5 (N P : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) :
    (N * P).toBlocks₂₁ = N.toBlocks₂₁ * P.toBlocks₁₁ + N.toBlocks₂₂ * P.toBlocks₂₁ := by sorry

alias «PI».«DatumBlockEigen».«Main».«toBlocks₂₁_mul'» := P2M_PI_DatumBlockEigen_Main_toBlocks___mul__15850fd75cb5
