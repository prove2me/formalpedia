-- Prove2me | Theorems.Thm_P2M_PI_Dv_Tr_normAt_zero__9806172384b3
-- name    : P2M_PI_Dv_Tr_normAt_zero__9806172384b3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:56:57.470969+00:00
-- url     : https://prove2.me/theorems/858a50de-3185-4cde-9df1-a401251b69bf
-- title:
--   P2 M PI Dv Tr norm At zero  9806172384b3: P2 M PI Dv Tr norm At zero  9806172384b3
-- statement:
--   The P2 M PI Dv Tr norm At zero  9806172384b3 construction uses the P2 M PI Dv Tr norm At zero  9806172384b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L159-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L159-L166

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem P2M_PI_Dv_Tr_normAt_zero__9806172384b3 (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) :
    Formalism.HermitianLatticesTheory.normAt b X v 0 = 0 := by sorry

alias «PI».«Dv».«Tr».«normAt_zero'» := P2M_PI_Dv_Tr_normAt_zero__9806172384b3
