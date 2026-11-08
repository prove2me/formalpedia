-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
-- name    : QEC.Coding.TannerLiftedProduct.cosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:48:41.457771+00:00
-- url     : https://prove2.me/theorems/e76ccec3-9569-4d08-a0af-b1888221c482
-- title:
--   Tanner Lifted Product: coset Leader Matrix is Delta Minimal of fiber Locally Minimal
-- statement:
--   The concrete Tanner geometry supplies the column-minimality hypothesis of
--   the PK22 local-star argument. Together with rowwise coset leaders, it makes
--   the selected product-kernel representative beta*w-minimal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1504-L1534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1504-L1534

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

theorem QEC.Coding.TannerLiftedProduct.cosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (ProductExpansion.row x₀ i) = z i)
    (J₃ : Finset W) (m : Nat) (beta : ℝ)
    (hJ₃ : Fintype.card W - 2 * m ≤ J₃.card)
    (hAgree : ∀ i ∈ J₃, ∀ j,
      localFaceMatrix label c v i j =
        ProductExpansion.cosetLeaderMatrix h z x₀ hx₀ i j)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    ProductExpansion.IsDeltaMinimal h
      (ProductExpansion.generatorImageParityCheck g')
      (beta * Fintype.card W)
      (ProductExpansion.cosetLeaderMatrix h z x₀ hx₀) := by sorry
