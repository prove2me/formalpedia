-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_ker_jointTensorMap
-- name    : QEC.Coding.HypergraphProduct.finrank_ker_jointTensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:33:08.411745+00:00
-- url     : https://prove2.me/theorems/1a9ec5d7-dc19-4a9a-9da3-fbf4d6aacba4
-- title:
--   Hypergraph Product: finrank ker joint Tensor Map
-- statement:
--   The joint tensor-kernel formula for arbitrary finite-dimensional maps.
--   No surjectivity assumption remains: each map is first corestricted to its
--   actual range.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Coordinates.lean#L21-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Coordinates.lean#L21-L75

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Coordinates
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct

theorem QEC.Coding.HypergraphProduct.finrank_ker_jointTensorMap
    {F : Type u} {M M' N N' : Type v}
    [Field F]
    [AddCommGroup M] [Module F M] [Module.Free F M] [Module.Finite F M]
    [AddCommGroup M'] [Module F M'] [Module.Free F M'] [Module.Finite F M']
    [AddCommGroup N] [Module F N] [Module.Free F N] [Module.Finite F N]
    [AddCommGroup N'] [Module F N'] [Module.Free F N'] [Module.Finite F N']
    (f : M →ₗ[F] M') (g : N →ₗ[F] N') :
    Module.finrank F (LinearMap.ker (jointTensorMap f g)) =
      Module.finrank F (LinearMap.ker f) *
        Module.finrank F (LinearMap.ker g) := by sorry
