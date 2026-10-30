-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_tensor_product_degradability
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.tensor_product_degradability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:01:06.388903+00:00
-- url     : https://prove2.me/theorems/63f7b2cd-80ca-4a82-b6f8-a4b9c55d0217
-- title:
--   Degradability of an independent tensor product
-- statement:
--   Let $R:\mathcal B(H_A)\to\mathcal B(H_B)$ and $S:\mathcal B(H_C)\to\mathcal B(H_D)$ be quantum channels, with all four spaces finite-dimensional and nonzero. Their tensor product is defined on all operators, including correlated inputs. Then
--
--   $$(R\text{ degradable and }S\text{ degradable})\iff R\otimes S\text{ degradable}.$$
--
--   This is a tensor-product assertion, not a statement about orthogonally flagged channels. Its fermionic use requires the fixed graded identification for disjoint, parity-respecting factors; no such identification is silently changed here.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 8, Lemma S7

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Lemma S7: an independent tensor product is degradable iff
BOTH factors are. Nonzero finite input/output spaces permit the converse's
fixed auxiliary state; no antidegradability analogue is silently substituted. -/
theorem tensor_product_degradability {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (R : Superop A B) (S : Superop C D) (hR : IsChannel R) (hS : IsChannel S) :
    (ChannelDegradable R ∧ ChannelDegradable S) ↔ ChannelDegradable (tensorChannel R S) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
