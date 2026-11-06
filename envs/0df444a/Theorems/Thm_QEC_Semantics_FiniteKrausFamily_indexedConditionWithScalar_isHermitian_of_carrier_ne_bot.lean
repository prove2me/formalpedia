-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedConditionWithScalar_isHermitian_of_carrier_ne_bot
-- name    : QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_isHermitian_of_carrier_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:34:54.803417+00:00
-- url     : https://prove2.me/theorems/295751b5-e411-4440-a51b-c1583d77fc22
-- title:
--   Finite Kraus Family: indexed Condition With Scalar is Hermitian of carrier ne bot
-- statement:
--   On a nonzero code carrier, indexed KL scalar data is a Hermitian matrix.
--
--   The proof evaluates the KL relation on a fixed nonzero code vector and cancels
--   its nonzero self-inner-product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L179-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L179-L211

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

theorem QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_isHermitian_of_carrier_ne_bot
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hC : C.carrier ≠ ⊥)
    (hKL : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    (Matrix.of fun i j => scalar i j).IsHermitian := by sorry
