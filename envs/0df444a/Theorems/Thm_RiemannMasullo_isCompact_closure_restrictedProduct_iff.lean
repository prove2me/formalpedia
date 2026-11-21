-- Prove2me | Theorems.Thm_RiemannMasullo_isCompact_closure_restrictedProduct_iff
-- name    : RiemannMasullo.isCompact_closure_restrictedProduct_iff
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:21:24.366867+00:00
-- url     : https://prove2.me/theorems/1b239c89-0e46-42d2-8c9d-cdf38965136e
-- title:
--   Compact closures in restricted products
-- statement:
--   In a restricted product of Hausdorff spaces whose distinguished sets are compact and open outside finitely many indices, a subset has compact closure exactly when it is contained in a product of compact sets that agree with the distinguished sets outside finitely many indices.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean#L88-L124

import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

open Filter Function Set Topology RestrictedProduct
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ i, TopologicalSpace (G i)]

namespace RiemannMasullo

theorem isCompact_closure_restrictedProduct_iff {A : (i : ι) → Set (G i)} [∀ i, T2Space (G i)]
    (hA : ∀ᶠ i in cofinite, IsCompact (A i) ∧ IsOpen (A i)) (H : Set (Πʳ i, [G i, A i])) :
    IsCompact (closure H) ↔ ∃ B : (i : ι) → Set (G i), (∀ i, IsCompact (B i)) ∧
      (∀ᶠ i in cofinite, B i = A i) ∧ ∀ x ∈ H, ∀ i, x i ∈ B i := by sorry

end RiemannMasullo
