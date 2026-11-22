-- Prove2me | Theorems.Thm_PettisIntegral_weakIntegral_comp_continuousLinearMap
-- name    : PettisIntegral.weakIntegral_comp_continuousLinearMap
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:31.441231+00:00
-- url     : https://prove2.me/theorems/127fee89-5a7f-4ff5-9d1e-ac752c721a81
-- title:
--   Lemma C.4.3.8 — weak integrals and Pettis integrals commute with continuous linear maps
-- statement:
--   **Vector-valued integrals commute with continuous linear maps (Lemma C.4.3.8).** Let $T\colon E_1\to E_2$ be a continuous linear map between Hausdorff locally convex spaces over $\mathbb k\in\{\mathbb R,\mathbb C\}$, let $(X,\mu)$ be a measure space and let $f\colon X\to E_1$ be a function. Write $T'\colon E_2'\to E_1'$, $T'(\varphi)=\varphi\circ T$, for the transpose of $T$ and $(T')^*\colon(E_1')^*\to(E_2')^*$, $\lambda\mapsto\lambda\circ T'$, for its algebraic transpose.
--
--   1. If $f$ is weakly $\mu$-integrable, then so is $T\circ f$, and the weak integrals satisfy
--   $$\int_X(T\circ f)\,d\mu=(T')^*\Bigl(\int_X f\,d\mu\Bigr)\qquad\text{in }(E_2')^*,$$
--   that is, $\bigl\langle\int_X(T\circ f)\,d\mu,\varphi\bigr\rangle=\bigl\langle\int_X f\,d\mu,\varphi\circ T\bigr\rangle$ for every $\varphi\in E_2'$.
--   2. If $f$ is $\mu$-integrable in the sense of Pettis, then so is $T\circ f$, and
--   $$\int_X(T\circ f)\,d\mu=T\Bigl(\int_X f\,d\mu\Bigr)\qquad\text{in }E_2.$$
--
--   This is the basic functoriality of the weak integral. It is what allows one to move continuous operators and evaluations through an integral sign; the paper records it, together with the seminorm estimate of Lemma C.4.3.9, as one of the two basic properties of the integral in the sense of Pettis.
--
--   **Formalization Note.** `WeaklyIntegrable`, `weakIntegral` and `HasPettisIntegral` are from `Def_PettisIntegral_Basic`; the weak integral is a function on the continuous dual, and $(T')^*$ is written out as evaluation at `φ.comp T`. Part 2 is stated for every Pettis integral $a$ of $f$: `HasPettisIntegral 𝕜 μ f a → HasPettisIntegral 𝕜 μ (T ∘ f) (T a)`. "Hausdorff locally convex" is `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]`. The statement does not involve a topology on $X$ and is given for an arbitrary (positive) measure space; the source has $X$ locally compact Hausdorff, $\mu$ a finite complex Radon measure and $\mathbb k=\mathbb C$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 714-715, Lemma C.4.3.8, (C.4.3.5) and (C.4.3.6)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- Weak integrals and Pettis integrals commute with continuous linear maps. -/
theorem weakIntegral_comp_continuousLinearMap {𝕜 E F X : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [PolynormableSpace 𝕜 F] [T2Space F]
    [MeasurableSpace X] (μ : Measure X) (f : X → E) (T : E →L[𝕜] F) :
    (WeaklyIntegrable 𝕜 μ f →
      WeaklyIntegrable 𝕜 μ (fun x => T (f x)) ∧
        ∀ φ : StrongDual 𝕜 F,
          weakIntegral 𝕜 μ (fun x => T (f x)) φ = weakIntegral 𝕜 μ f (φ.comp T)) ∧
    ∀ a : E, HasPettisIntegral 𝕜 μ f a → HasPettisIntegral 𝕜 μ (fun x => T (f x)) (T a) := by
  sorry

end PettisIntegral
