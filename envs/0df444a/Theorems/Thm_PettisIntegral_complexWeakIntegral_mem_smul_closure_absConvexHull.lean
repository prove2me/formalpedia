-- Prove2me | Theorems.Thm_PettisIntegral_complexWeakIntegral_mem_smul_closure_absConvexHull
-- name    : PettisIntegral.complexWeakIntegral_mem_smul_closure_absConvexHull
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:58.745578+00:00
-- url     : https://prove2.me/theorems/9264e5fd-1d5a-4a53-8772-358170509fc4
-- title:
--   Lemma C.4.3.1 — mean value theorem for weak integrals against a complex Radon measure: $\int_X f\,d\mu\in\|\mu\|\cdot\overline{\mathrm{cch}}(f(X))$
-- statement:
--   **Mean value theorem for a complex Radon measure (Lemma C.4.3.1).** Let $X$ be a non-empty locally compact Hausdorff space, $\mu$ a finite complex Radon measure on $X$ with total variation $|\mu|$ and norm $\|\mu\|=|\mu|(X)$, let $E$ be a Hausdorff locally convex space over $\mathbb C$, and let $f\colon X\to E$ be continuous and weakly $\mu$-integrable. Then the weak integral $\int_X f\,d\mu\in(E')^*$, the linear form $\varphi\mapsto\int_X\varphi(f(x))\,d\mu(x)$ on $E'$, satisfies
--   $$\int_X f\,d\mu\ \in\ \|\mu\|\cdot\overline{\mathrm{cch}}\bigl(f(X)\bigr),$$
--   where $\overline{\mathrm{cch}}(f(X))$ is the closure, in the weak completion $(E')^*$ with the topology $\sigma((E')^*,E')$, of the convex circled (absolutely convex) hull of the image of $f$ (embedded by $\iota_E\colon E\to(E')^*$).
--
--   For a positive measure the convex hull suffices (this is the published positive-measure form); for a complex measure the phases of $\mu$ force the circled hull. The theorem locates the weak integral, which a priori is only a point of the weak completion; when the closed absolutely convex hull of $f(X)$ is compact in $E$ it yields a vector of $E$, which is Pettis' integrability criterion.
--
--   **Formalization Note.** `complexWeakIntegral μ f` and `ComplexWeaklyIntegrable μ f` are the notions of `Def_PettisIntegral_ComplexMeasure`, and `toWeakCompletion ℂ` is $\iota_E$ from `Def_PettisIntegral_Basic`. The weak completion is represented in the product space `StrongDual ℂ E → ℂ` (product topology), where the closure is taken; the absolutely convex hull of a set $S$ is `convexHull ℝ (balancedHull ℂ S)`; the factor $\|\mu\|$ is `(μ.variation Set.univ).toReal` and acts by pointwise scalar multiplication of sets. "finite complex Radon measure" is `(μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]` on a locally compact Hausdorff space with its Borel $\sigma$-algebra: the total variation $|\mu|$ (`μ.variation`) is a finite regular Borel measure (a complex Borel measure is Radon if and only if its total variation is). "Hausdorff locally convex space" is `[IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]`. **Deviation from the source.** `[Nonempty X]` is assumed: for $X=\emptyset$ the hull is empty while the integral is $0$ (the source identifies the hull with a bipolar, which always contains $0$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 711, Lemma C.4.3.1; classical reference: for a positive measure, N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. VI, §1, no. 2, p. VI.5, Prop. 5 (as cited by the paper)

import Mathlib
import Definitions.Def_PettisIntegral_Basic
import Definitions.Def_PettisIntegral_ComplexMeasure

open MeasureTheory
open scoped Pointwise

set_option autoImplicit false

namespace PettisIntegral

/-- Mean-value theorem for weak integrals against a finite complex Radon measure: the weak
integral of a continuous weakly integrable function lies in `|μ|(X)` times the closure, in the
weak completion, of the absolutely convex (convex circled) hull of the image of the function. -/
theorem complexWeakIntegral_mem_smul_closure_absConvexHull {E X : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X] (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → E) (hf : Continuous f) (hfi : ComplexWeaklyIntegrable μ f) :
    complexWeakIntegral μ f ∈
      (μ.variation Set.univ).toReal •
        closure (convexHull ℝ (balancedHull ℂ
          (Set.range fun x : X => toWeakCompletion ℂ (f x)))) := by sorry

end PettisIntegral
