-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P04_trivialisingSystem_smallTransitions
-- name    : QAlgorithms.Papers.Independent.Intake100.P04.trivialisingSystem_smallTransitions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:43:38.380934+00:00
-- url     : https://prove2.me/theorems/4ff912af-de68-4e39-8dc8-fc220b401707
-- title:
--   Refinement with transition images in prescribed open sets
-- statement:
--   Let $X$ be a compact Hausdorff space, let $K$ be a topological group, and let $P\to X$ be a locally trivial continuous right principal $K$-bundle. Fix a finite continuous open trivialising system $\mathcal U=(U_i,\sigma_i)_{i=1}^n$ and an open cover $(O_\ell)_{\ell\in L}$ of $K$. There is a finite continuous open trivialising system $\mathcal V=(V_s,\tau_s)_{s=1}^r$ refining $\mathcal U$, including restriction of its sections, such that
--
--   $$
--   \forall s,t\in\{1,\ldots,r\}\;\exists\ell\in L:\quad
--   k_{st}(V_s\cap V_t)\subseteq O_\ell,
--   $$
--
--   where the transition function is determined by $\tau_s(x)\,k_{st}(x)=\tau_t(x)$. Refinement means that there is an index map $a$ with $V_s\subseteq U_{a(s)}$ and $\tau_s=\sigma_{a(s)}|_{V_s}$.
--
--   This permits simultaneous control of the transition functions without changing the local sections. The member $O_\ell$ may depend on the ordered pair $(s,t)$.
--
--   **Formalization Note** A continuous free right action together with the supplied section and coordinate laws expresses the actual principal local trivializations. No positive-cardinality hypothesis is added, so the empty-base case is included.
-- source:
--   Lie Group Structures on Symmetry Groups of Principal Bundles, arXiv:math/0612522v1, PDF p. 27, Lemma A.21

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P04

namespace QAlgorithms.Papers.Independent.Intake100.P04

open Set Filter Topology

open QAlgorithms.Papers.Independent.Next46.P35

open QAlgorithms.Papers.Independent.Bridge50.P08 (HasLeftVelocity identityDifferential)

open QAlgorithms.Papers.Independent.Gap48.P05 (ExponentialLieData)

universe u v w z

attribute [local instance] QAlgorithms.Papers.Independent.Intake100.P04.productCharts

section ContinuousBundles

variable {K : Type u} {X : Type v} {P : Type w}

variable [Group K] [TopologicalSpace K] [TopologicalSpace X] [TopologicalSpace P]

/-- Lemma A.21, PDF p. 27: a finite refinement, restricting the given
sections, whose each ordered transition function has image in one member
of the prescribed open cover of K. The cover member may depend on both
refined indices. Compact spaces use the customary Hausdorff principal-bundle
convention; K need only be a topological group. -/
theorem trivialisingSystem_smallTransitions
    [IsTopologicalGroup K] [CompactSpace X] [T2Space X]
    (B : RightBundleData (K := K) (X := X) (P := P))
    (n : ℕ) (U : OpenTrivialisingSystem B (Fin n))
    {L : Type z} (O : L → Set K)
    (hOpen : ∀ l, IsOpen (O l)) (hCover : ∀ k : K, ∃ l, k ∈ O l) :
    ∃ r : ℕ, ∃ V : OpenTrivialisingSystem B (Fin r),
      Refines V U ∧ ∀ s t : Fin r, ∃ l : L,
        ∀ x ∈ V.base s ∩ V.base t, transitionFunction V s t x ∈ O l := by sorry

end ContinuousBundles

end QAlgorithms.Papers.Independent.Intake100.P04
