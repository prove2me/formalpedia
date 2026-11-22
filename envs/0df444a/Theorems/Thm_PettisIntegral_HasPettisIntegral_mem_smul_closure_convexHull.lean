-- Prove2me | Theorems.Thm_PettisIntegral_HasPettisIntegral_mem_smul_closure_convexHull
-- name    : PettisIntegral.HasPettisIntegral.mem_smul_closure_convexHull
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:28.650427+00:00
-- url     : https://prove2.me/theorems/88ed2be4-be97-4d33-885d-739e357140d0
-- title:
--   Mean-Value Theorem for Pettis integrals: $\int_X f\,d\mu\in\mu(X)\cdot\overline{\mathrm{ch}}(f(X))$, the closed convex hull being taken in $E$
-- statement:
--   **Mean-Value Theorem for Pettis integrals.** Let $X$ be a non-empty locally compact Hausdorff space, $\mu$ a finite positive Radon measure on $X$, $E$ a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$, and $f\colon X\to E$ a continuous function which is $\mu$-integrable in the sense of Pettis, with integral $\int_X f\,d\mu\in E$. Then
--   $$\int_X f\,d\mu\ \in\ \mu(X)\cdot\overline{\mathrm{ch}}\bigl(f(X)\bigr),$$
--   where $\overline{\mathrm{ch}}(f(X))$ is the closed convex hull of the image of $f$ in $E$ (closure for the given topology of $E$). In particular, for a probability measure the integral is a point of the closed convex hull of the values of $f$.
--
--   This is the form of the Mean-Value Theorem (Lemma C.4.3.1 of the paper) inside $E$: the lemma places the weak integral in $\mu(X)$ times the closure of the convex hull of $f(X)$ in the weak completion $(E')^*$, and by Lemma C.4.1.2(1) the closure of a convex subset of $E$ for the given topology coincides with its closure for the weak topology $\sigma(E,E')$, which is the topology induced by $(E')^*$. The paper combines the two in the proof of Pettis' integrability criterion (Theorem C.4.3.5). The statement is the basic a priori localisation of a vector-valued integral.
--
--   **Deviation from the source.** The source's Lemma C.4.3.1 is stated for a finite complex Radon measure, with the factor $\|\mu\|$ and the closed convex circled hull in the weak completion. Here $\mu$ is positive (the classical case), the convex hull suffices, and the conclusion is stated in $E$ for a function that has a Pettis integral. The space $X$ is assumed non-empty: for $X=\emptyset$ the convex hull is empty while the integral is $0$.
--
--   **Formalization Note.** `HasPettisIntegral 𝕜 μ f a` (from `Def_PettisIntegral_Basic`) says that $a$ is the Pettis integral of $f$. The convex hull is `convexHull ℝ`, for the real vector space structure `[Module ℝ E] [IsScalarTower ℝ 𝕜 E]` underlying the $\mathbb k$-structure, and `(μ Set.univ).toReal • S` is the pointwise multiplication of a set by the real number $\mu(X)$. "Finite positive Radon measure" is `[IsFiniteMeasure μ] [μ.Regular]` on the Borel $\sigma$-algebra; "Hausdorff locally convex" is `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 711, Lemma C.4.3.1 (Mean-Value Theorem), combined with Lemma C.4.1.2(1), p. 710, as in the proof of Theorem C.4.3.5, p. 714; classical reference: N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. VI, §1, no. 2, Prop. 5, p. VI.5 (cited by the paper for the case of a real-valued positive measure)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory
open scoped Pointwise

set_option autoImplicit false

namespace PettisIntegral

/-- Mean-value theorem for Pettis integrals: the Pettis integral of a continuous function against
a finite positive Radon measure lies in `μ(X)` times the closed convex hull of the image of the
function. -/
theorem HasPettisIntegral.mem_smul_closure_convexHull {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X] {μ : Measure X} [IsFiniteMeasure μ] [μ.Regular] {f : X → E} (hf : Continuous f)
    {a : E} (ha : HasPettisIntegral 𝕜 μ f a) :
    a ∈ (μ Set.univ).toReal • closure (convexHull ℝ (Set.range f)) := by sorry

end PettisIntegral
