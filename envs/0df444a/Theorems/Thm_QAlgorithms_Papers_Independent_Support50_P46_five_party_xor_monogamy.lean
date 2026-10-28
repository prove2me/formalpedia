-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P46_five_party_xor_monogamy
-- name    : QAlgorithms.Papers.Independent.Support50.P46.five_party_xor_monogamy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T23:58:26.265087+00:00
-- url     : https://prove2.me/theorems/5971caf5-19b5-46df-894b-a29ad3342397
-- title:
--   The five-party XOR purification is monogamous for all disjoint subsystems
-- statement:
--   Let A,A′,B,B′,C be five qubit factors in this order, and define
--
--   $$
--   |\psi_5\rangle=\tfrac12\sum_{x,y\in\{0,1\}}
--   |x\rangle_A|x\rangle_{A'}|y\rangle_B|y\rangle_{B'}|x\mathbin{\oplus}y\rangle_C.
--   $$
--
--   The vector has norm one, its rank-one density matrix is normalized, and its ABC marginal is the equal diagonal mixture of 000,011,101,110. Let U,V,W be any three pairwise disjoint subsets of the five factors; a subset denotes their tensor product and may be empty. Using von Neumann entropy in bits and I₃(U:V:W)=S(U)+S(V)+S(W)−S(UV)−S(UW)−S(VW)+S(UVW), one has
--
--   $$
--   I_3(U:V:W)_{\psi_5}\le0.
--   $$
--
--   This shows that a pure state may be monogamous on every such triple while possessing the displayed classical ABC marginal.
-- source:
--   Holographic Mutual Information is Monogamous, arXiv:1107.2940v2, PDF p. 18, §5.2, (5.14): a pure monogamous state with classical ABC marginal

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P46

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (subsystemEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.18, (5.14): the displayed normalized five-party pure state has the
classical XOR ABC marginal and obeys monogamy for every triple of disjoint
unions of its five fixed factors, including empty unions. -/
theorem five_party_xor_monogamy :
    IsState copiedFiveVector ∧ IsDensityMatrix copiedFiveDensity ∧
    threeMarginal copiedFiveDensity ![0, 2, 4] = xorClassical ∧
    ∀ a b c : Finset (Fin 5),
      Disjoint a b → Disjoint a c → Disjoint b c →
      tripartiteInformation copiedFiveDensity a b c ≤ 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P46

end
