-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_ker_jointTensorMap_of_surjective
-- name    : QEC.Coding.HypergraphProduct.finrank_ker_jointTensorMap_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:30:22.676219+00:00
-- url     : https://prove2.me/theorems/7e3f6695-9498-4349-aeb1-d6e10cd4031d
-- title:
--   Hypergraph Product: finrank ker joint Tensor Map of surjective
-- statement:
--   For surjective maps, the simultaneous tensor kernel has dimension equal
--   to the product of the two ordinary kernel dimensions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension.lean#L37-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension.lean#L37-L95

import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct

theorem QEC.Coding.HypergraphProduct.finrank_ker_jointTensorMap_of_surjective
    {F : Type u} {M M' N N' : Type v}
    [Field F]
    [AddCommGroup M] [Module F M] [Module.Free F M] [Module.Finite F M]
    [AddCommGroup M'] [Module F M'] [Module.Free F M'] [Module.Finite F M']
    [AddCommGroup N] [Module F N] [Module.Free F N] [Module.Finite F N]
    [AddCommGroup N'] [Module F N'] [Module.Free F N'] [Module.Finite F N']
    (f : M →ₗ[F] M') (g : N →ₗ[F] N')
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Module.finrank F (LinearMap.ker (jointTensorMap f g)) =
      Module.finrank F (LinearMap.ker f) *
        Module.finrank F (LinearMap.ker g) := by sorry
