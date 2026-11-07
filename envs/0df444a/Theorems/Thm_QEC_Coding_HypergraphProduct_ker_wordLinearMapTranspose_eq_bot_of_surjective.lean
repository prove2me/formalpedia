-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_ker_wordLinearMapTranspose_eq_bot_of_surjective
-- name    : QEC.Coding.HypergraphProduct.ker_wordLinearMapTranspose_eq_bot_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:21:36.233951+00:00
-- url     : https://prove2.me/theorems/6c8159cb-c123-4bc4-b5b5-8fe97f675499
-- title:
--   Hypergraph Product: ker word Linear Map Transpose eq bot of surjective
-- statement:
--   Surjectivity of a finite-coordinate map forces the kernel of its transpose
--   to vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L28-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L28-L46

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.ker_wordLinearMapTranspose_eq_bot_of_surjective
    {F : Type v} {A B : Type u}
    [Field F] [Fintype F]
    [Fintype A] [Fintype B]
    (f : Word F A →ₗ[F] Word F B) (hf : Function.Surjective f) :
    LinearMap.ker (wordLinearMapTranspose f) = ⊥ := by sorry
