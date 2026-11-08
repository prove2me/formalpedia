-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_centeredAdjacencyEuclidean_rightCayleyGraph_eq_conj
-- name    : QEC.Coding.TannerLiftedProduct.centeredAdjacencyEuclidean_rightCayleyGraph_eq_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:23:57.841628+00:00
-- url     : https://prove2.me/theorems/63a94ca5-a48a-430e-ba1d-d1090bab9e93
-- title:
--   Tanner Lifted Product: centered Adjacency Euclidean right Cayley Graph eq conj
-- statement:
--   Centered Euclidean Cayley adjacency is conjugate to the centered
--   right-regular operator on the ordinary function space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L311-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L311-L323

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

theorem QEC.Coding.TannerLiftedProduct.centeredAdjacencyEuclidean_rightCayleyGraph_eq_conj
    (label : W → G) :
    SmallSetExpansion.centeredAdjacencyEuclidean
        (rightCayleyGraph label) (Fintype.card W) =
      (cayleyEuclideanLinearEquiv (G := G)).conj
        (cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyCenteredGeneratorSum label)) := by sorry
