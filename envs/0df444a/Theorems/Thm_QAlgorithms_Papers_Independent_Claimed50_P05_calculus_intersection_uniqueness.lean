-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_intersection_uniqueness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_intersection_uniqueness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:14:14.319781+00:00
-- url     : https://prove2.me/theorems/04fbf49a-778e-4aa4-a694-c69e2025d952
-- title:
--   Corollary 5.10
-- statement:
--   Let $S,T\subseteq k$ be Borel sets and let $\Phi$ and $\Psi$ be Borel calculi on $S$ and $T$ on the same $H$. Suppose both send the restricted identity symbol to the same operator graph $A$. Then
--
--   $$\Phi\text{ and }\Psi\text{ are concentrated on }S\cap T,\qquad\Phi_{S\cap T}=\Psi_{S\cap T}.$$
--
--   Concentration is interpreted within each original base. The induced calculi are formed by extending to $k$ through restriction of symbols and then restricting to the intersection by zero extension.
--
--   This compares calculi originally defined on different Borel bases.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 24, Corollary 5.10

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Corollary 5.10, PDF p.24: common concentration and equality of induced calculi on the intersection. -/
theorem calculus_intersection_uniqueness (S T : Set k) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (F : Symbol S k → Relation H) (G : Symbol T k → Relation H)
    (hF : Calculus F) (hG : Calculus G)
    (hA : F ⟨Subtype.val, measurable_subtype_coe⟩ = G ⟨Subtype.val, measurable_subtype_coe⟩) :
    Concentrated F {x : S | x.val ∈ T} ∧ Concentrated G {x : T | x.val ∈ S} ∧
    restrictBase (extendBase F) (S ∩ T) (hS.inter hT) =
      restrictBase (extendBase G) (S ∩ T) (hS.inter hT) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
