-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P46_copied_xor_violation
-- name    : QAlgorithms.Papers.Independent.Support50.P46.copied_xor_violation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T23:57:45.008499+00:00
-- url     : https://prove2.me/theorems/7ef3c7eb-ec23-406d-a537-5470b9b8ae45
-- title:
--   The six-party copied XOR purification violates monogamy
-- statement:
--   Let A,A′,B,B′,C,C′ be six qubit factors, in this order. Put
--
--   $$
--   |\psi_6\rangle=\tfrac12\sum_{x,y\in\{0,1\}}
--   |x\rangle_A|x\rangle_{A'}|y\rangle_B|y\rangle_{B'}|x\mathbin{\oplus}y\rangle_C|x\mathbin{\oplus}y\rangle_{C'}.
--   $$
--
--   Here ⊕ is addition modulo two. This vector has norm one, its rank-one density matrix is normalized, and its ABC marginal is the equal diagonal mixture of 000,011,101,110. For entropy in bits and I₃(U:V:W)=S(U)+S(V)+S(W)−S(UV)−S(UW)−S(VW)+S(UVW),
--
--   $$
--   I_3(A:A':BC)_{\psi_6}=1.
--   $$
--
--   BC retains only B and C, not their copies. Thus this purification violates monogamy, independently of the incorrect preceding general identity.
-- source:
--   Holographic Mutual Information is Monogamous, arXiv:1107.2940v2, PDF p. 17, §5.2: the six-party copied XOR purification violates monogamy

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P46

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (subsystemEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.17, (5.13) and the following paragraph: copied XOR purification
has I3(A:A-copy:BC)=1 bit and hence violates mutual-information monogamy.
This does not rely on the false general identity preceding that paragraph. -/
theorem copied_xor_violation :
    IsState copiedSixVector ∧ IsDensityMatrix copiedSixDensity ∧
    threeMarginal copiedSixDensity ![0, 2, 4] = xorClassical ∧
    tripartiteInformation copiedSixDensity {0} {1} {2, 4} = 1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P46

end
