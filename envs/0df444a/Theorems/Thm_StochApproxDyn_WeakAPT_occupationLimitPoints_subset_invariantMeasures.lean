-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_occupationLimitPoints_subset_invariantMeasures
-- name    : StochApproxDyn.WeakAPT.occupationLimitPoints_subset_invariantMeasures
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:23:59.028008+00:00
-- url     : https://prove2.me/theorems/25498b0b-bc5a-4b5b-be7f-df8983940dc7
-- title:
--   Theorem 10.1: weak limit points of the occupation measures of a weak asymptotic pseudotrajectory are invariant
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\{\mathcal F_t:t\ge0\}$ a nondecreasing family of sub-$\sigma$-algebras. Let $(M,d)$ be a separable metric space with its Borel $\sigma$-algebra and $\Phi$ a semiflow on $M$. Let $X:\mathbb R_+\times\Omega\to M$ be a weak asymptotic pseudotrajectory of $\Phi$, with occupation measures $\mu_t(\omega)=\frac1t\int_0^t\delta_{X(s,\omega)}\,ds$ and set of weak limit points $\mathcal M(X,\omega)\subset\mathcal P(M)$ as $t\to\infty$. Let $\mathcal M(\Phi)$ be the set of $\Phi$-invariant Borel probability measures.
--
--   **Theorem 10.1.** There exists a set $\tilde\Omega\subset\Omega$ of full measure, $P(\tilde\Omega)=1$, such that for all $\omega\in\tilde\Omega$
--   $$\mathcal M(X,\omega)\subset\mathcal M(\Phi).$$
--
--   No compactness is assumed: $\mathcal M(X,\omega)$ may be empty, in which case the inclusion is trivial. When the occupation measures are tight (for example when the path has compact closure), $\mathcal M(X,\omega)$ is nonempty and the theorem says that the long-run statistics of the process are described by invariant measures of the deterministic dynamics.
--
--   **Formalization Note** "There exists a set of full measure on which ..." is stated as "for $P$-almost every $\omega$ ...". Invariance is $(\Phi_t)_*\mu=\mu$ for all $t\ge0$ (see the definition of $\mathcal M(\Phi)$). Weak limit points are cluster points as $t\to\infty$ in Mathlib's `ProbabilityMeasure M`.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 10, p. 61 (PDF p. 62), Theorem 10.1

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_InvariantMeasures
import Definitions.Def_StochApproxDyn_WeakAPT_OccupationMeasure
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), Theorem 10.1, p. 61: if `X` is a weak asymptotic pseudotrajectory of the
semiflow `Φ` on a separable metric space `M`, then for `P`-almost every `ω` every weak limit point
of the occupation measures `μ_t(ω)` is `Φ`-invariant: `𝓜(X, ω) ⊂ 𝓜(Φ)`. -/
theorem occupationLimitPoints_subset_invariantMeasures
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X) :
    ∀ᵐ ω ∂P, occupationLimitPoints X ω ⊆ invariantMeasures Φ := by sorry

end StochApproxDyn.WeakAPT
