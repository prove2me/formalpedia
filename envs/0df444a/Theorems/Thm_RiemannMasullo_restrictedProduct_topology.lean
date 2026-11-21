-- Prove2me | Theorems.Thm_RiemannMasullo_restrictedProduct_topology
-- name    : RiemannMasullo.restrictedProduct_topology
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:28:43.855365+00:00
-- url     : https://prove2.me/theorems/58f8cc07-72fe-4bb3-9f1b-de5456a4cde3
-- title:
--   Masullo Lemma A.1.1.2 on the topology of restricted products
-- statement:
--   Under the hypotheses of Definition A.1.1.1 the restricted product is a locally compact Hausdorff topological group. Finite changes of distinguished subgroups preserve its topology, compact closures are characterized by compact coordinate boxes, and finitely many factors split off continuously. The final openness claim uses the upstream hypothesis of openness outside the chosen finite set.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L113-L144

import Mathlib

open Filter Function Topology
open scoped RestrictedProduct
variable {ι : Type*} (G : ι → Type*) [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
  (K : (i : ι) → Subgroup (G i)) (I₀ : Finset ι)
  (h₀ : ∀ i ∈ I₀, K i = ⊥) (h₁ : ∀ i ∉ I₀, IsCompact (K i : Set (G i)) ∧ IsOpen (K i : Set (G i)))
include h₀ h₁

namespace RiemannMasullo

theorem restrictedProduct_topology :
    let P := Πʳ i, [G i, K i]
    (T2Space P ∧ LocallyCompactSpace P ∧ IsTopologicalGroup P) ∧
    (∀ K' : (i : ι) → Subgroup (G i), (∀ i ∈ I₀, K' i = ⊥) →
      (∀ i ∉ I₀, IsCompact (K' i : Set (G i)) ∧ IsOpen (K' i : Set (G i))) →
      (∀ᶠ i in cofinite, K' i = K i) →
      ∃ e : (Πʳ i, [G i, K' i]) ≃ₜ* P, ∀ x i, e x i = x i) ∧
    (∀ H : Set P, IsCompact (closure H) ↔
      ∃ B : (i : ι) → Set (G i), (∀ i, IsCompact (B i)) ∧
        (∀ᶠ i in cofinite, B i = K i) ∧ ∀ x ∈ H, ∀ i, x i ∈ B i) ∧
    (∀ J : Finset ι, ∃ e : P ≃ₜ* (((j : J) → G j) ×
      (Πʳ j : {i // i ∉ J}, [G j, K j])),
      ∀ x, (∀ j, (e x).1 j = x j) ∧ ∀ j, (e x).2 j = x j) ∧
    (∀ J : Finset ι, (∀ i ∉ J, IsOpen (K i : Set (G i))) →
      ∀ U : (i : ι) → Set (G i), (∀ i ∈ J, IsOpen (U i)) →
      IsOpen {x : P | (∀ i ∈ J, x i ∈ U i) ∧ ∀ i ∉ J, x i ∈ K i}) := by sorry

end RiemannMasullo
