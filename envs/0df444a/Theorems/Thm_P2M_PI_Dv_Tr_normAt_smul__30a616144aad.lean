-- Prove2me | Theorems.Thm_P2M_PI_Dv_Tr_normAt_smul__30a616144aad
-- name    : P2M_PI_Dv_Tr_normAt_smul__30a616144aad
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:21.889003+00:00
-- url     : https://prove2.me/theorems/d57203c6-ad90-40e4-9482-e7ea95e253b9
-- title:
--   P2 M PI Dv Tr norm At smul  30a616144aad: P2 M PI Dv Tr norm At smul  30a616144aad
-- statement:
--   The P2 M PI Dv Tr norm At smul  30a616144aad construction uses the P2 M PI Dv Tr norm At smul  30a616144aad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L134-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/NormAtAddLe.lean#L134-L140

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

theorem P2M_PI_Dv_Tr_normAt_smul__30a616144aad (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (c : K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (c • x) = ‖v.embedding c‖ * Formalism.HermitianLatticesTheory.normAt b X v x := by sorry

alias «PI».«Dv».«Tr».«normAt_smul'» := P2M_PI_Dv_Tr_normAt_smul__30a616144aad
