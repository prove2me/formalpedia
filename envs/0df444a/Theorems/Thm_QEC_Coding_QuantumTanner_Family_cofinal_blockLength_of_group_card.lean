-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Family_cofinal_blockLength_of_group_card
-- name    : QEC.Coding.QuantumTanner.Family.cofinal_blockLength_of_group_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:01:30.303413+00:00
-- url     : https://prove2.me/theorems/37fd7d04-a58f-452b-ab60-7f9bd692316f
-- title:
--   Family: cofinal block Length of group card
-- statement:
--   At a fixed positive degree, cofinal group cardinality implies cofinal
--   physical length by double-counting the actual square incidences.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SpectralFamily.lean#L25-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SpectralFamily.lean#L25-L46

import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
import Definitions.Def_QEC_Coding_QuantumTanner_SpectralFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe u v
open QEC.Coding.QuantumTanner.Family

theorem QEC.Coding.QuantumTanner.Family.cofinal_blockLength_of_group_card
    {Index : Type u} {G A B Square XBasis ZBasis : Index → Type v}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (Square i)]
    [∀ i, Fintype (XBasis i)] [∀ i, Fintype (ZBasis i)]
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (Delta : Nat) (hDelta : 0 < Delta)
    (hA : ∀ i, Fintype.card (A i) = Delta)
    (hB : ∀ i, Fintype.card (B i) = Delta)
    (hGroups : ∀ N : Nat, ∃ i, N ≤ Fintype.card (G i)) :
    ∀ N : Nat, ∃ i, N ≤ (family i).blockLength := by sorry
