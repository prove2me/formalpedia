-- Prove2me | Theorems.Thm_Rudin_ch02_finite_intersection_property
-- name    : Rudin.ch02_finite_intersection_property
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:49:23.00552+00:00
-- url     : https://prove2.me/theorems/756d6bc6-6f56-419c-8c4e-c06b28c46b0e
-- title:
--   Theorem 2.36 — the finite intersection property
-- statement:
--   Let $\mathcal{K}$ be a nonempty collection of compact subsets of a metric space such that every nonempty finite subcollection has nonempty intersection. Then $\bigcap \mathcal{K} \ne \varnothing$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 38, Theorem 2.36

import Mathlib

namespace Rudin

/-- Rudin, Theorem 2.36: if a nonempty collection of compact sets has the property that every
finite subcollection has nonempty intersection, then the intersection of the whole collection is
nonempty. -/
theorem ch02_finite_intersection_property {X : Type*} [MetricSpace X] (𝒦 : Set (Set X))
    (hne : 𝒦.Nonempty) (hcomp : ∀ K ∈ 𝒦, IsCompact K)
    (hfin : ∀ ℱ ⊆ 𝒦, ℱ.Finite → ℱ.Nonempty → (⋂₀ ℱ).Nonempty) :
    (⋂₀ 𝒦).Nonempty := by sorry

end Rudin
