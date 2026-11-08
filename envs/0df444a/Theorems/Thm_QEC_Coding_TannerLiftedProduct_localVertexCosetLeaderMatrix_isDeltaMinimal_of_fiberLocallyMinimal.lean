-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localVertexCosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
-- name    : QEC.Coding.TannerLiftedProduct.localVertexCosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:16.12652+00:00
-- url     : https://prove2.me/theorems/5100e24f-4670-4e04-9034-9f5f353b1bbd
-- title:
--   Tanner Lifted Product: local Vertex Coset Leader Matrix is Delta Minimal of fiber Locally Minimal
-- statement:
--   The concrete active-vertex coset-leader witness is beta*w-minimal on the
--   large-agreement branch of the Tanner-star argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1538-L1570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1538-L1570

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

theorem QEC.Coding.TannerLiftedProduct.localVertexCosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (m : Nat) (beta : ℝ)
    (hJ₃ : Fintype.card W - 2 * m ≤
      (localAgreementDirections label h hRank g' c v).card)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    ProductExpansion.IsDeltaMinimal h
      (ProductExpansion.generatorImageParityCheck g')
      (beta * Fintype.card W)
      (localVertexCosetLeaderMatrix h hRank g' c v) := by sorry
