-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexUnitaryMix_diagonalizes_indexedProjectorConditionWithScalar
-- name    : QEC.Semantics.FiniteKrausFamily.indexUnitaryMix_diagonalizes_indexedProjectorConditionWithScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:16:51.68952+00:00
-- url     : https://prove2.me/theorems/2a3dbf84-4752-467f-a84a-b2cafd235778
-- title:
--   Finite Kraus Family: index Unitary Mix diagonalizes indexed Projector Condition With Scalar
-- statement:
--   The Finite Kraus Family construction uses the index Unitary Mix diagonalizes indexed Projector Condition With Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L796-L819
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L796-L819

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
variable [DecidableEq ι]

theorem QEC.Semantics.FiniteKrausFamily.indexUnitaryMix_diagonalizes_indexedProjectorConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hPSD : (Matrix.of fun i j => scalar i j).PosSemidef)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar) :
    ∃ U : Matrix.unitaryGroup ι Complex,
      IndexedKnillLaflammeProjectorConditionWithScalar (E.indexUnitaryMix U) C
        (fun a b : ι =>
          Matrix.diagonal (fun i : ι =>
            (hPSD.1.eigenvalues i : Complex)) a b) ∧
      ∀ i : ι, 0 ≤ hPSD.1.eigenvalues i := by sorry
