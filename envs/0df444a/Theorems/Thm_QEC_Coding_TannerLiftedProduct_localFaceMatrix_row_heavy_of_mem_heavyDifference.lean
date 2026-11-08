-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_row_heavy_of_mem_heavyDifference
-- name    : QEC.Coding.TannerLiftedProduct.localFaceMatrix_row_heavy_of_mem_heavyDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:35:48.712992+00:00
-- url     : https://prove2.me/theorems/e0a774d2-2613-4eb9-b47c-7dbb6ded5333
-- title:
--   Tanner Lifted Product: local Face Matrix row heavy of mem heavy Difference
-- statement:
--   Every nonzero inactive difference row is heavy: its local-code distance
--   and the coset-leader inequality force the corresponding face row to carry at
--   least half that distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L788-L833
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L788-L833

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.localFaceMatrix_row_heavy_of_mem_heavyDifference
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hc : LiftedProduct.boundary1 (data label h h') c = 0)
    (d : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (v : VertexIndex G) (b : W)
    (hb : b ∈ localHeavyDifferenceDirections label h hRank h' c v) :
    d ≤ 2 * HammingWeight
      (ProductExpansion.row (localFaceMatrix label c v) b) := by sorry
