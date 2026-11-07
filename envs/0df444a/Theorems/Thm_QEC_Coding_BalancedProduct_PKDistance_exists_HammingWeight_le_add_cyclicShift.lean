-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_HammingWeight_le_add_cyclicShift
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_HammingWeight_le_add_cyclicShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:06.590048+00:00
-- url     : https://prove2.me/theorems/301a28ec-d374-4cac-8fd3-05a540aa7890
-- title:
--   PKDistance: exists Hamming Weight le add cyclic Shift
-- statement:
--   If every cyclic fibre uses at most half of its coordinates, one cyclic
--   difference has weight at least that of the original word.
--
--   Source: [PK20, Lemma `lm:autcorr`].
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L279-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L279-L291

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w

theorem QEC.Coding.BalancedProduct.PKDistance.exists_HammingWeight_le_add_cyclicShift
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ Fintype.card G) :
    ∃ t : G, HammingWeight z ≤ HammingWeight (z + cyclicShift t z) := by sorry
