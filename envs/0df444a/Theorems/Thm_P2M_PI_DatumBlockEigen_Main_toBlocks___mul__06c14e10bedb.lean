-- Prove2me | Theorems.Thm_P2M_PI_DatumBlockEigen_Main_toBlocks___mul__06c14e10bedb
-- name    : P2M_PI_DatumBlockEigen_Main_toBlocks___mul__06c14e10bedb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:58.575878+00:00
-- url     : https://prove2.me/theorems/d2fc681d-5b9f-5251-a879-27309e94ff97
-- title:
--   P2 M PI Datum Block Eigen Main to Blocks   mul  06c14e10bedb: P2 M PI Datum Block Eigen Main to Blocks   mul  06c14e10bedb
-- statement:
--   The P2 M PI Datum Block Eigen Main to Blocks   mul  06c14e10bedb construction uses the P2 M PI Datum Block Eigen Main to Blocks   mul  06c14e10bedb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L32-L36

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

theorem P2M_PI_DatumBlockEigen_Main_toBlocks___mul__06c14e10bedb (N P : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) :
    (N * P).toBlocks₁₁ = N.toBlocks₁₁ * P.toBlocks₁₁ + N.toBlocks₁₂ * P.toBlocks₂₁ := by sorry

alias «PI».«DatumBlockEigen».«Main».«toBlocks₁₁_mul'» := P2M_PI_DatumBlockEigen_Main_toBlocks___mul__06c14e10bedb
