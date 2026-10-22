-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P05_boundedComposition_adjoint
-- name    : QAlgorithms.Papers.Independent.Gap48.P05.boundedComposition_adjoint
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:06:12.18788+00:00
-- url     : https://prove2.me/theorems/bd69a305-7528-4a2a-a35d-4718833526a0
-- title:
--   Bounded compositions and domains of adjoints
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space, $A\in B(\mathcal H)$, and $B:\mathcal D(B)\to\mathcal H$ a densely defined complex-linear operator. Then
--
--   $$
--   AB\text{ is bounded on }\mathcal D(B)
--   \quad\Longleftrightarrow\quad A^*\mathcal H\subseteq\mathcal D(B^*).
--   $$
--
--   When these conditions hold, $(AB)^*=B^*A^*$, with both adjoints having domain all of $\mathcal H$. If $B^*$ is densely defined as well, then
--
--   $$
--   A^*B^*\text{ is bounded on }\mathcal D(B^*)
--   \quad\Longleftrightarrow\quad A\mathcal H\subseteq\mathcal D(\overline B),
--   $$
--
--   and in this case $\overline B A$ is everywhere defined and bounded. All bounds use the ambient Hilbert norm. These statements relate boundedness on a dense domain to range inclusions in adjoint or closure domains.
-- source:
--   Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups, arXiv:1505.02659v2, PDF p. 9, Lemma 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P05

namespace QAlgorithms.Papers.Independent.Gap48.P05

open Set Filter Topology

open QAlgorithms.Papers.Independent.Claimed50.P22

open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

attribute [local instance] QAlgorithms.Papers.Independent.Gap48.P05.productCharts

section PartialOperators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 2.1, PDF p. 9, both clauses. The PDF has D(closure B) and
(closure B) A in (b). B need not be closed. Density is retained for B,
and separately for B* in (b), guarding Mathlib's non-dense adjoint default.
Equality of adjoints is stated with all domains explicit. -/
theorem boundedComposition_adjoint
    (A : H →L[ℂ] H) (B : H →ₗ.[ℂ] H) (hDense : Dense (B.domain : Set H)) :
    (PMapBounded (A.toLinearMap.compPMap B) ↔
      ∀ v : H, A.adjoint v ∈ B.adjoint.domain) ∧
    (PMapBounded (A.toLinearMap.compPMap B) →
      ∀ v : H, ∃ h1 : v ∈ (A.toLinearMap.compPMap B).adjoint.domain,
        ∃ h2 : A.adjoint v ∈ B.adjoint.domain,
          (A.toLinearMap.compPMap B).adjoint ⟨v, h1⟩ =
            B.adjoint ⟨A.adjoint v, h2⟩) ∧
    (Dense (B.adjoint.domain : Set H) →
      (PMapBounded (A.adjoint.toLinearMap.compPMap B.adjoint) ↔
        ∀ v : H, A v ∈ B.closure.domain) ∧
      ((∀ v : H, A v ∈ B.closure.domain) →
        ∃ T : H →L[ℂ] H, ∀ v : H, ∃ hv : A v ∈ B.closure.domain,
          T v = B.closure ⟨A v, hv⟩)) := by sorry

end PartialOperators

end QAlgorithms.Papers.Independent.Gap48.P05
