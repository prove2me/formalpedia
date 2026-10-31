-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P15_bigonQuotient_plotCriterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P15.bigonQuotient_plotCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:16:06.922307+00:00
-- url     : https://prove2.me/theorems/90ed4fc2-186c-4a86-bb01-92d8510634f7
-- title:
--   Lemma 2.4: bigon quotient plot criterion
-- statement:
--   Let $X$ and $M$ be finite-dimensional Hausdorff, second-countable real smooth manifolds without boundary. Let $BX$ be the space of smooth bigons with uniform sitting instants on each bigon. Let $p:BX\to Q$ be the named surjective bigon quotient projection, and give $Q$ the quotient diffeology. A map $f:Q\to M$ is diffeological if and only if, for every $k\ge0$, every open $U\subseteq\mathbb R^k$, and every family $c:U\to BX$ with smooth evaluation $(u,s,t)\mapsto c(u)(s,t)$, the composite is smooth:
--
--   $$f\circ p\circ c:U\longrightarrow M.$$
--
--   This tests smoothness on the quotient using parametrized bigons and requires only local lifts of quotient plots. No classification of the other bigon quotient relations is asserted.
--
--   **Formalization Note** Bigons use their constant sitting extensions to the plane. The diffeologies are generated using Mathlib's full Euclidean plots; the criterion still quantifies over arbitrary open domains, including dimension zero. Sitting instants are individual to each bigon, with no uniformity imposed on a family.
-- source:
--   Smooth Functors vs. Differential Forms, arXiv:0802.0663v4, PDF p. 17, Lemma 2.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P15

namespace QAlgorithms.Papers.Independent.Intake100.P15

open scoped Manifold ContDiff

universe u v w z

section BigonPlots

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {X : Type u} [TopologicalSpace X] [ChartedSpace E X]

/-- Lemma 2.4, PDF p. 17: the full open-plot criterion for maps from
bigon quotients. The named surjection p represents pr_i with quotient
diffeology; no classification of the unspecified other quotients is used.
Sitting extensions identify the displayed evaluation on the square with
the globally extended evaluation used here. Both implications are stated. -/
theorem bigonQuotient_plotCriterion
    [FiniteDimensional ℝ E] [T2Space X] [SecondCountableTopology X]
    [IsManifold (𝓘(ℝ, E)) ∞ X]
    {F : Type z} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace F M]
    [T2Space M] [SecondCountableTopology M] [IsManifold (𝓘(ℝ, F)) ∞ M]
    {Q : Type v} (p : SittingBigon E X → Q) (hProjection : Function.Surjective p)
    (f : Q → M) :
    @Diffeology.DSmooth Q M (bigonQuotientDiffeology p)
      (manifoldDiffeology (E := F)) f ↔
    ∀ (k : ℕ) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)))
      (c : U → SittingBigon E X),
      ContMDiff
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin k))).prod
          ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))))
        (𝓘(ℝ, E)) ∞ (fun z : U × (ℝ × ℝ) => (c z.1).map z.2) →
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (𝓘(ℝ, F)) ∞
        (fun u : U => f (p (c u))) := by sorry

end BigonPlots

end QAlgorithms.Papers.Independent.Intake100.P15
