-- Prove2me | Theorems.Thm_RiemannMasullo_continuous_restrictedProduct_of_uniform
-- name    : RiemannMasullo.continuous_restrictedProduct_of_uniform
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:21:24.71697+00:00
-- url     : https://prove2.me/theorems/b0fc4d39-e820-4412-89a8-cbbfafcb3c46
-- title:
--   Continuity into a restricted product under uniform finite exceptions
-- statement:
--   A coordinatewise continuous map to a restricted product is continuous if all its values lie in the distinguished sets on a single cofinite set of indices.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean#L24-L31

import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

open Filter Function Set Topology RestrictedProduct
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ i, TopologicalSpace (G i)]

namespace RiemannMasullo

theorem continuous_restrictedProduct_of_uniform {X : Type*} [TopologicalSpace X]
    {A : (i : ι) → Set (G i)} {f : X → Πʳ i, [G i, A i]}
    (hc : ∀ i, Continuous (fun x ↦ f x i)) (hA : ∀ᶠ i in cofinite, ∀ x, f x i ∈ A i) :
    Continuous f := by sorry

end RiemannMasullo
