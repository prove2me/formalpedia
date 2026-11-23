-- Prove2me | Theorems.Thm_P2M_PI_Dv_Tr_normAt_sum_le__185993638e0c
-- name    : P2M_PI_Dv_Tr_normAt_sum_le__185993638e0c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:30.628267+00:00
-- url     : https://prove2.me/theorems/f369bf4f-25ff-4edb-8f20-e67137a699cf
-- title:
--   P2 M PI Dv Tr norm At sum le  185993638e0c: P2 M PI Dv Tr norm At sum le  185993638e0c
-- statement:
--   The P2 M PI Dv Tr norm At sum le  185993638e0c construction uses the P2 M PI Dv Tr norm At sum le  185993638e0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L168-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L168-L171

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

theorem P2M_PI_Dv_Tr_normAt_sum_le__185993638e0c {α : Type} (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (s : Finset α) (f : α → V) :
    Formalism.HermitianLatticesTheory.normAt b X v (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Formalism.HermitianLatticesTheory.normAt b X v (f i) := by sorry

alias «PI».«Dv».«Tr».«normAt_sum_le'» := P2M_PI_Dv_Tr_normAt_sum_le__185993638e0c
