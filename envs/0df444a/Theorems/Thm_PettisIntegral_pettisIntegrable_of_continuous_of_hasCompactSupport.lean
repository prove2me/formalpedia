-- Prove2me | Theorems.Thm_PettisIntegral_pettisIntegrable_of_continuous_of_hasCompactSupport
-- name    : PettisIntegral.pettisIntegrable_of_continuous_of_hasCompactSupport
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:30.982869+00:00
-- url     : https://prove2.me/theorems/2462c5d8-3622-4ed3-b919-903d92d01144
-- title:
--   Theorem C.4.3.5 (Pettis' integrability criterion) — continuous compactly supported functions with values in a quasi-complete locally convex space are Pettis integrable
-- statement:
--   **Pettis' integrability criterion (Theorem C.4.3.5).** Let $X$ be a locally compact Hausdorff space and $\mu$ a finite positive Radon measure on $X$. Let $E$ be a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$ which is *quasi-complete*, i.e. every bounded closed subset of $E$ is complete. Let $f\colon X\to E$ be a continuous function with compact support. Then $f$ is $\mu$-integrable in the sense of Pettis: there is a (unique) vector $\int_X f\,d\mu\in E$ such that
--   $$\varphi\Bigl(\int_X f\,d\mu\Bigr)=\int_X\varphi(f(x))\,d\mu(x)\qquad\text{for all }\varphi\in E',$$
--   where $E'$ is the continuous dual of $E$.
--
--   A priori the weak integral $\varphi\mapsto\int_X\varphi\circ f\,d\mu$ is only an element of the weak completion $(E')^*$ of $E$; the theorem says that for a continuous compactly supported function with values in a quasi-complete space it is represented by a vector of $E$. This is the basic existence theorem for vector-valued integrals (Gelfand–Pettis integrals); the paper specializes it to $E$ a Hilbert space and to $E$ the space of bounded operators on a Hilbert space $H$ with the strong operator topology, which is quasi-complete (Remark C.4.3.13) but not complete when $H$ is infinite-dimensional and separable (Remark C.4.3.4).
--
--   **Deviation from the source.** The source allows a finite complex Radon measure; the statement is given for a finite positive Radon measure (the complex case follows by decomposing the measure into positive parts).
--
--   **Formalization Note.** `PettisIntegrable 𝕜 μ f` is from `Def_PettisIntegral_Basic`. $E$ carries a uniform structure compatible with its additive group (`[UniformSpace E] [IsUniformAddGroup E]`), with respect to which Mathlib's `QuasiCompleteSpace 𝕜 E` is formulated; "Hausdorff locally convex" is `[ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]`. "Finite positive Radon measure" is `[IsFiniteMeasure μ] [μ.Regular]` on the Borel $\sigma$-algebra (`[BorelSpace X]`). The source works over $\mathbb C$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 713, Theorem C.4.3.5 (Pettis' Integrability Criterion); classical reference: A. Grothendieck, Sur certains espaces de fonctions holomorphes. I, J. reine angew. Math. 192 (1953), pp. 35-64, Lemme 2, and H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. II, Corollary to 4.3 (both as cited by the paper)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- Pettis' integrability criterion: a continuous compactly supported function on a locally
compact Hausdorff space with values in a quasi-complete Hausdorff locally convex space is Pettis
integrable for every finite positive Radon measure. -/
theorem pettisIntegrable_of_continuous_of_hasCompactSupport {𝕜 E X : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (f : X → E) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    PettisIntegrable 𝕜 μ f := by sorry

end PettisIntegral
