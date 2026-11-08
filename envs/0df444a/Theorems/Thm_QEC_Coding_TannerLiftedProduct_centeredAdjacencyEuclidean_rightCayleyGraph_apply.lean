-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_centeredAdjacencyEuclidean_rightCayleyGraph_apply
-- name    : QEC.Coding.TannerLiftedProduct.centeredAdjacencyEuclidean_rightCayleyGraph_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:12:43.84398+00:00
-- url     : https://prove2.me/theorems/a183f50b-a6e2-48da-a318-f423f65ea0f1
-- title:
--   Tanner Lifted Product: centered Adjacency Euclidean right Cayley Graph apply
-- statement:
--   The centered Euclidean adjacency operator of a labelled Cayley graph is
--   exactly the right-regular action of the centered generator-sum element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L291-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L291-L301

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]

theorem QEC.Coding.TannerLiftedProduct.centeredAdjacencyEuclidean_rightCayleyGraph_apply
    (label : W → G) (f : EuclideanSpace ℂ G) (g : G) :
    SmallSetExpansion.centeredAdjacencyEuclidean
        (rightCayleyGraph label) (Fintype.card W) f g =
      (cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyCenteredGeneratorSum label) (fun h => f h)) g := by sorry
