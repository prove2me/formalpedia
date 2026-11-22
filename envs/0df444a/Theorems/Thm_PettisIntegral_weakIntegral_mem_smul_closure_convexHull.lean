-- Prove2me | Theorems.Thm_PettisIntegral_weakIntegral_mem_smul_closure_convexHull
-- name    : PettisIntegral.weakIntegral_mem_smul_closure_convexHull
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:28.064821+00:00
-- url     : https://prove2.me/theorems/eb37fae3-c0b9-4982-9422-6f029e1c298d
-- title:
--   Lemma C.4.3.1 (Mean-Value Theorem) — the weak integral lies in $\mu(X)$ times the closed convex hull of $f(X)$ in the weak completion $(E')^*$
-- statement:
--   **Mean-Value Theorem for weak integrals (Lemma C.4.3.1).** Let $X$ be a non-empty locally compact Hausdorff space, $\mu$ a finite positive Radon measure on $X$, $E$ a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$ with continuous dual $E'$, and $f\colon X\to E$ a continuous, weakly $\mu$-integrable function. Let $\int_X f\,d\mu\in(E')^*$ be its weak integral, the linear form $\varphi\mapsto\int_X\varphi(f(x))\,d\mu(x)$ on $E'$, and let $\iota_E\colon E\to(E')^*$ be the canonical map $\iota_E(u)(\varphi)=\varphi(u)$. Then
--   $$\int_X f\,d\mu\ \in\ \mu(X)\cdot\overline{\mathrm{ch}}\bigl(f(X)\bigr),$$
--   where $\overline{\mathrm{ch}}(f(X))$ denotes the closure, in the weak completion $(E')^*$ for the topology $\sigma((E')^*,E')$, of the convex hull of $\iota_E(f(X))$.
--
--   The closure has to be taken in $(E')^*$: the map $\iota_E$ is in general not closed, and the closure of the convex hull in $E$ and in $(E')^*$ may differ (they agree when the closure in $E$ is compact). The lemma is the first step towards integrability criteria: if the closed convex hull of $f(X)$ in $E$ is compact, the weak integral is forced to lie in $\iota_E(E)$. The paper uses it in the proof of Pettis' integrability criterion (Theorem C.4.3.5) and of Theorem C.4.3.2(2).
--
--   **Deviation from the source.** The source states the lemma for a finite *complex* Radon measure $\mu$, with the factor $\|\mu\|=|\mu|(X)$ and the closed convex *circled* hull $\overline{\mathrm{cch}}(f(X))$. The statement given here is the case of a positive measure, which is the case the source attributes to Bourbaki; for a positive measure the convex hull suffices, and this is a sharper conclusion since $\overline{\mathrm{ch}}\subseteq\overline{\mathrm{cch}}$. The space $X$ is assumed non-empty: for $X=\emptyset$ the convex hull is empty while the integral is $0$.
--
--   **Formalization Note.** `weakIntegral 𝕜 μ f` and `toWeakCompletion 𝕜` are from `Def_PettisIntegral_Basic`; they are functions `StrongDual 𝕜 E → 𝕜`, and the closure is taken in this function space with the product topology, which is the closure in $(E')^*$ for $\sigma((E')^*,E')$ because the linear forms are a closed subspace of the product. The convex hull is `convexHull ℝ`, and `(μ Set.univ).toReal • S` is the pointwise multiplication of the set $S$ by the real number $\mu(X)$. "Finite positive Radon measure" is `[IsFiniteMeasure μ] [μ.Regular]` on the Borel $\sigma$-algebra (`[BorelSpace X]`). "Hausdorff locally convex" is `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]`; the source works over $\mathbb C$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 711, Lemma C.4.3.1 (Mean-Value Theorem); classical reference: N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. VI, §1, no. 2, Prop. 5, p. VI.5 (cited by the paper for the case of a real-valued positive measure)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory
open scoped Pointwise

set_option autoImplicit false

namespace PettisIntegral

/-- Mean-value theorem for weak integrals: the weak integral of a continuous weakly integrable
function against a finite positive Radon measure lies in `μ(X)` times the closure, in the weak
completion, of the convex hull of the image of the function. -/
theorem weakIntegral_mem_smul_closure_convexHull {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X] (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (f : X → E) (hf : Continuous f)
    (hfi : WeaklyIntegrable 𝕜 μ f) :
    weakIntegral 𝕜 μ f ∈
      (μ Set.univ).toReal •
        closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x))) := by sorry

end PettisIntegral
