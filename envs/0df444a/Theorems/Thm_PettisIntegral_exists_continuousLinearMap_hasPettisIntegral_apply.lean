-- Prove2me | Theorems.Thm_PettisIntegral_exists_continuousLinearMap_hasPettisIntegral_apply
-- name    : PettisIntegral.exists_continuousLinearMap_hasPettisIntegral_apply
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:44.91958+00:00
-- url     : https://prove2.me/theorems/4b68d47a-df55-42ac-91f3-ad2067d236d6
-- title:
--   Lemma C.4.3.11 — operator-valued integrals on a Hilbert space: $u\mapsto\int_X f(x)u\,d\mu(x)$ is a bounded operator of norm $\le\int_X\|f(x)\|\,d\mu(x)$
-- statement:
--   **Operator-valued integrals on a Hilbert space (Lemma C.4.3.11).** Let $H$ be a Hilbert space over $\mathbb k\in\{\mathbb R,\mathbb C\}$ and $\mathscr B(H)$ the space of bounded linear operators on $H$. Let $(X,\mu)$ be a measure space with $\mu$ a positive measure, and let $f\colon X\to\mathscr B(H)$ be a function such that
--
--   1. for every $u\in H$ the function $x\mapsto f(x)u\in H$ is weakly measurable (i.e. $x\mapsto\varphi(f(x)u)$ is $\mu$-measurable for every continuous linear form $\varphi$ on $H$);
--   2. the function $x\mapsto\|f(x)\|$ (operator norm) is $\mu$-measurable and $\mu$-integrable.
--
--   Then for every $u\in H$ the function $x\mapsto f(x)u$ is $\mu$-integrable in the sense of Pettis, and the map
--   $$T\colon H\to H,\qquad T u=\int_X f(x)u\,d\mu(x)$$
--   is a bounded linear operator on $H$, with
--   $$\|T\|\ \le\ \int_X\|f(x)\|\,d\mu(x).$$
--
--   No measurability of $f$ as a map into the Banach space $\mathscr B(H)$ is assumed, so $f$ need not be Bochner integrable; the integral $\int_X f\,d\mu$ is defined pointwise (in the strong operator topology). This is how operators such as $\pi(\phi)=\int_G\phi(g)\pi(g)\,dg$ are defined for unitary representations. In the paper it is deduced from the integrability of weakly integrable functions with values in a reflexive space and the seminorm estimate for Pettis integrals.
--
--   **Formalization Note.** `WeaklyMeasurable 𝕜 μ g` and `HasPettisIntegral 𝕜 μ g a` are the notions of `Def_PettisIntegral_Basic` ("$\mu$-measurable" is `AEMeasurable`); hypothesis 2 is `Integrable (fun x => ‖f x‖) μ`, which includes almost everywhere measurability. The conclusion is the existence of `T : H →L[𝕜] H` with `HasPettisIntegral 𝕜 μ (fun x => f x u) (T u)` for all `u` and `‖T‖ ≤ ∫ x, ‖f x‖ ∂μ`. The norm bound is the estimate (C.4.3.14) of the source's proof; the lemma itself only asserts boundedness. The statement is given for a positive measure on an arbitrary measure space and over `[RCLike 𝕜]`; the source takes $X$ locally compact Hausdorff, $\mu$ a finite complex Radon measure and $\mathbb k=\mathbb C$ (the complex case follows from the positive one applied to $|\mu|$ and to $x\mapsto h(x)f(x)$, where $d\mu=h\,d|\mu|$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 715-716, Lemma C.4.3.11 and (C.4.3.14)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- Operator-valued integrals on a Hilbert space: if `x ↦ f x u` is weakly measurable for every
`u` and `x ↦ ‖f x‖` is integrable, then `u ↦ ∫ f x u ∂μ` (Pettis integrals) is a bounded operator,
of norm at most `∫ ‖f x‖ ∂μ`. -/
theorem exists_continuousLinearMap_hasPettisIntegral_apply {𝕜 H X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [MeasurableSpace X]
    (μ : Measure X) (f : X → H →L[𝕜] H)
    (hmeas : ∀ u : H, WeaklyMeasurable 𝕜 μ (fun x => f x u))
    (hint : Integrable (fun x => ‖f x‖) μ) :
    ∃ T : H →L[𝕜] H, (∀ u : H, HasPettisIntegral 𝕜 μ (fun x => f x u) (T u)) ∧
      ‖T‖ ≤ ∫ x, ‖f x‖ ∂μ := by sorry

end PettisIntegral
