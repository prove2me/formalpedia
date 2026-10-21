-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_tensor_complementarity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.tensor_complementarity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:40:53.275328+00:00
-- url     : https://prove2.me/theorems/6ac22256-6cf9-4f6d-9865-24db57c290bf
-- title:
--   Tensor products preserve complementarity
-- statement:
--   For arbitrary finite linear dilations $V_i:H_{A_i}\to H_{B_i}\otimes H_{C_i}$, with nonzero input spaces, define the regrouped product dilation by
--
--   $$V_{((b_1,b_2),(c_1,c_2)),(a_1,a_2)}=(V_1)_{(b_1,c_1),a_1}(V_2)_{(b_2,c_2),a_2}.$$
--
--   Its receiver map is the tensor product of the two receiver maps, and its environmental map is the tensor product of their complements. Consequently the two tensor-product maps are complementary. These are full-map identities on every joint operator, including entangled inputs; the displayed regrouping fixes the factor permutation.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 4, Tensor products preserve complementarity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- PDF p.4: explicitly regrouped superopTensor dilation and full-map equality. -/
theorem tensor_complementarity [Nonempty A] [Nonempty A2]
    (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ) :
    receiverChannel (tensorDilation V W) = superopTensor (receiverChannel V) (receiverChannel W) ∧
    complementaryChannel (tensorDilation V W) = superopTensor (complementaryChannel V) (complementaryChannel W) ∧
    CPComplementary (superopTensor (receiverChannel V) (receiverChannel W))
      (superopTensor (complementaryChannel V) (complementaryChannel W)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
