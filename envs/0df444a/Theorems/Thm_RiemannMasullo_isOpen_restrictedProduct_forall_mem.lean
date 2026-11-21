-- Prove2me | Theorems.Thm_RiemannMasullo_isOpen_restrictedProduct_forall_mem
-- name    : RiemannMasullo.isOpen_restrictedProduct_forall_mem
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:21:24.530872+00:00
-- url     : https://prove2.me/theorems/1ec849fb-6e58-4e45-9760-957d2b35abe6
-- title:
--   Open coordinate conditions in a restricted product
-- statement:
--   Imposing distinguished-set membership at every index in a specified subset is an open condition on the restricted product, provided the distinguished sets at those indices are open.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean#L35-L47

import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

open Filter Function Set Topology RestrictedProduct
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ i, TopologicalSpace (G i)]

namespace RiemannMasullo

theorem isOpen_restrictedProduct_forall_mem {A : (i : ι) → Set (G i)} (t : Set ι)
    (ht : ∀ i ∈ t, IsOpen (A i)) :
    IsOpen {x : Πʳ i, [G i, A i] | ∀ i ∈ t, x i ∈ A i} := by sorry

end RiemannMasullo
