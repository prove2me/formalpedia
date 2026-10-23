-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P11_exampleUnknownQubit
-- name    : QAlgorithms.Papers.Independent.Gap20.P11.exampleUnknownQubit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:17:51.744995+00:00
-- url     : https://prove2.me/theorems/8e87037b-9cbf-422e-8144-cef11afc3dbe
-- title:
--   An uncorrelated unknown qubit costs one qubit
-- statement:
--   Alice holds a maximally mixed qubit and Bob has a trivial register, so $\rho_{AB}=(I_A/2)\otimes|0\rangle\langle0|_B$. The state may be purified by an inaccessible reference. With entropy in bits,
--
--   $$
--   S(A\mid B)=1,\qquad e\text{ is an achievable merging cost}\ \Longleftrightarrow\ e\ge1.
--   $$
--
--   One qubit suffices by direct transmission: the explicit code has a single two-dimensional quantum message and its encoding and decoding compose to the identity on every qubit operator. Alternatively, Alice can distribute one Bell pair by sending one of its halves and then teleport her qubit. The four normalized Bell-measurement branches form a complete instrument, and Bob's two-bit-conditioned corrections are channels. With that one supplied Bell pair, the teleportation protocol acts as the identity on every input operator, including every off-diagonal block of an arbitrary external reference.
--
--   The lower bound concerns unknown quantum information with its reference correlations, while the two constructions demonstrate the source's direct and teleportation alternatives.
-- source:
--   Quantum information can be negative, arXiv:quant-ph/0505062v1, PDF p. 3, Example 1: an uncorrelated maximally mixed qubit costs one qubit

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P11

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3–4, example 1: one qubit is necessary asymptotically, and both
direct transmission and teleportation using one distributed EPR pair work.
Teleportation is asserted on all operator blocks, hence also on an unknown
qubit entangled with an inaccessible reference. -/
theorem exampleUnknownQubit :
    IsDensityMatrix unknownQubit ∧ conditionalEntropy unknownQubit = 1 ∧
    (∀ rate : ℝ, MergingAchievable unknownQubit rate ↔ 1 ≤ rate) ∧
    directQubit.q = 1 ∧ IsChannel directQubit.encode ∧ IsChannel directQubit.decode ∧
    (∀ X : Matrix Bool Bool ℂ, directQubit.decode (directQubit.encode X) = X) ∧
    IsState (QAlgorithms.Papers.Independent.Information100.P22.bell Bool) ∧ IsKrausFamily teleportRow ∧
    (∀ s, IsChannel (conjSuperop (teleportCorrection s))) ∧
    (∀ (R : Type) [Fintype R] (X : Matrix (R × Bool) (R × Bool) ℂ),
      idTensorSuperop teleportOperation (teleportReferenceInput X) =
        fun p q : R × (Unit × Bool) => X (p.1, p.2.2) (q.1, q.2.2)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P11

end
