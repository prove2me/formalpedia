-- Prove2me | Theorems.Thm_RiemannMasullo_restrictedProduct_description
-- name    : RiemannMasullo.restrictedProduct_description
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:28:44.470337+00:00
-- url     : https://prove2.me/theorems/fe9717d2-4c9b-49a8-a649-340e5d5836e3
-- title:
--   Underlying set and identity neighborhoods of a restricted product
-- statement:
--   For locally compact Hausdorff commutative groups with distinguished compact open subgroups outside a finite exceptional set and trivial subgroups on it, the restricted product consists of the tuples in those subgroups almost everywhere. Boxes of identity neighborhoods that agree with the subgroups off finitely many indices form a neighborhood basis at the identity.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L54-L105

import Mathlib

open Filter Function Topology
open scoped RestrictedProduct
variable {ι : Type*} (G : ι → Type*) [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
  (K : (i : ι) → Subgroup (G i)) (I₀ : Finset ι)
  (h₀ : ∀ i ∈ I₀, K i = ⊥) (h₁ : ∀ i ∉ I₀, IsCompact (K i : Set (G i)) ∧ IsOpen (K i : Set (G i)))
include h₀ h₁

namespace RiemannMasullo

theorem restrictedProduct_description :
    Set.range (fun x : Πʳ i, [G i, K i] ↦ fun i ↦ x i) =
      {x | ∀ᶠ i in cofinite, x i ∈ K i} ∧
    (𝓝 (1 : Πʳ i, [G i, K i])).HasBasis
      (fun U : (i : ι) → Set (G i) ↦ (∀ i, U i ∈ 𝓝 1) ∧ ∀ᶠ i in cofinite, U i = K i)
      (fun U ↦ {x | ∀ i, x i ∈ U i}) := by sorry

end RiemannMasullo
