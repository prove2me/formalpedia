-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedConditionWithScalar_posSemidef_of_carrier_ne_bot
-- name    : QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_posSemidef_of_carrier_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:15:09.182197+00:00
-- url     : https://prove2.me/theorems/7fd92664-f96f-43f6-a745-26520f5a7862
-- title:
--   Finite Kraus Family: indexed Condition With Scalar pos Semidef of carrier ne bot
-- statement:
--   On a nonzero code carrier, indexed KL scalar data is positive semidefinite.
--
--   The scalar matrix is a nonnegative scalar multiple of the Gram matrix of the
--   vectors `E_i z` for any fixed nonzero code vector `z`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L219-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L219-L248

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

theorem QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_posSemidef_of_carrier_ne_bot
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hC : C.carrier ≠ ⊥)
    (hKL : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    (Matrix.of fun i j => scalar i j).PosSemidef := by sorry
