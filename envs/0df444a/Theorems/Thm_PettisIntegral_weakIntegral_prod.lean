-- Prove2me | Theorems.Thm_PettisIntegral_weakIntegral_prod
-- name    : PettisIntegral.weakIntegral_prod
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:42.248948+00:00
-- url     : https://prove2.me/theorems/96dac78e-e6dd-4b42-b0ae-290465093cf8
-- title:
--   Lemma C.4.4.1 — Fubini's theorem for weak integrals and integrals in the sense of Pettis
-- statement:
--   **Fubini's theorem for the integral in the sense of Pettis (Lemma C.4.4.1).** Let $E$ be a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$, let $(X,\mu)$ and $(Y,\nu)$ be measure spaces with $\sigma$-finite (more generally $s$-finite) positive measures, and let $f\colon X\times Y\to E$ be a weakly $(\mu\otimes\nu)$-integrable function. Assume:
--
--   1. the function $f(x,\cdot)\colon Y\to E$ is $\nu$-integrable in the sense of Pettis for every $x\in X$;
--   2. the function $f(\cdot,y)\colon X\to E$ is $\mu$-integrable in the sense of Pettis for every $y\in Y$.
--
--   Then the functions
--   $$x\longmapsto\int_Y f(x,y)\,d\nu(y)\in E\qquad\text{and}\qquad y\longmapsto\int_X f(x,y)\,d\mu(x)\in E$$
--   are weakly $\mu$-integrable on $X$ and weakly $\nu$-integrable on $Y$ respectively, and, as elements of the weak completion $(E')^*$,
--   $$\int_{X\times Y}f\,d(\mu\otimes\nu)=\int_Y\Bigl(\int_X f(x,y)\,d\mu(x)\Bigr)d\nu(y)=\int_X\Bigl(\int_Y f(x,y)\,d\nu(y)\Bigr)d\mu(x).$$
--   Explicitly, for every continuous linear form $\varphi$ on $E$ the three numbers obtained by applying $\varphi$ under the integral signs are equal.
--
--   The outer integrals are weak integrals: the lemma does not assert that they are represented by vectors of $E$. The paper states it in §C.4.4 (Fubini's Theorem and Weil's Integral Formula) as the version of Fubini's theorem it requires for the integral in the sense of Pettis.
--
--   **Formalization Note.** `WeaklyIntegrable`, `weakIntegral`, `PettisIntegrable` and `pettisIntegral` are from `Def_PettisIntegral_Basic`; weak integrals are functions on the continuous dual `StrongDual 𝕜 E`, and their equality is equality of functions. The product measure is Mathlib's `μ.prod ν` on the product $\sigma$-algebra of arbitrary measurable spaces, with `[SFinite μ] [SFinite ν]`. The source takes $X$, $Y$ locally compact Hausdorff and $\sigma$-compact with (complete) positive Radon measures, which are $\sigma$-finite; almost everywhere measurability in `WeaklyIntegrable` plays the role of measurability for the completed product measure. "Hausdorff locally convex" is `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]`; the source works over $\mathbb C$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 717, Lemma C.4.4.1 (see also Remark C.4.4.2, which relates the continuous compactly supported case to the Remark in N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. III, §4, p. III.43)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- Fubini's theorem for the integral in the sense of Pettis: if `f` is weakly integrable for the
product measure and all its partial functions are Pettis integrable, then the two functions of
partial Pettis integrals are weakly integrable and their weak integrals are the weak integral of
`f` for the product measure. -/
theorem weakIntegral_prod {𝕜 E X Y : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E]
    [T2Space E] [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (f : X × Y → E) (hf : WeaklyIntegrable 𝕜 (μ.prod ν) f)
    (hx : ∀ x : X, PettisIntegrable 𝕜 ν (fun y => f (x, y)))
    (hy : ∀ y : Y, PettisIntegrable 𝕜 μ (fun x => f (x, y))) :
    WeaklyIntegrable 𝕜 μ (fun x => pettisIntegral 𝕜 ν (fun y => f (x, y))) ∧
      WeaklyIntegrable 𝕜 ν (fun y => pettisIntegral 𝕜 μ (fun x => f (x, y))) ∧
      weakIntegral 𝕜 μ (fun x => pettisIntegral 𝕜 ν (fun y => f (x, y))) =
        weakIntegral 𝕜 (μ.prod ν) f ∧
      weakIntegral 𝕜 ν (fun y => pettisIntegral 𝕜 μ (fun x => f (x, y))) =
        weakIntegral 𝕜 (μ.prod ν) f := by sorry

end PettisIntegral
