-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_errorImageSubspace_inner_eq_zero_of_indexedConditionWithScalar
-- name    : QEC.Semantics.FiniteKrausFamily.errorImageSubspace_inner_eq_zero_of_indexedConditionWithScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:33:36.587684+00:00
-- url     : https://prove2.me/theorems/a8ac7302-93d5-4023-9c2f-477bd9902c6f
-- title:
--   Finite Kraus Family: error Image Subspace inner eq zero of indexed Condition With Scalar
-- statement:
--   If an indexed KL scalar vanishes, the corresponding error-image subspaces are
--   orthogonal in the concrete inner-product sense needed by recovery construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L58-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L58-L73

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.FiniteKrausFamily.errorImageSubspace_inner_eq_zero_of_indexedConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeConditionWithScalar E C scalar)
    {i j : ι} (hzero : scalar i j = 0) :
    ∀ x : H, x ∈ E.errorImageSubspace C i →
      ∀ y : H, y ∈ E.errorImageSubspace C j →
        inner Complex x y = 0 := by sorry
