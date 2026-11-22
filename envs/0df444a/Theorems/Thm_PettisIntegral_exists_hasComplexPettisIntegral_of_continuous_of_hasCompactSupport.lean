-- Prove2me | Theorems.Thm_PettisIntegral_exists_hasComplexPettisIntegral_of_continuous_of_hasCompactSupport
-- name    : PettisIntegral.exists_hasComplexPettisIntegral_of_continuous_of_hasCompactSupport
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:58.702798+00:00
-- url     : https://prove2.me/theorems/23eb9a21-5175-4a63-98e4-ab1269e72ced
-- title:
--   Theorem C.4.3.5 — Pettis' integrability criterion for a finite complex Radon measure
-- statement:
--   **Pettis' integrability criterion for a complex Radon measure (Theorem C.4.3.5).** Let $X$ be a locally compact Hausdorff space and $\mu$ a finite complex Radon measure on $X$. Let $E$ be a quasi-complete Hausdorff locally convex space over $\mathbb C$, and let $f\colon X\to E$ be continuous with compact support. Then $f$ is $\mu$-integrable in the sense of Pettis: there is a vector $a\in E$ such that $\varphi\circ f$ is $|\mu|$-integrable for every $\varphi\in E'$ and
--   $$\varphi(a)=\int_X\varphi(f(x))\,d\mu(x)\qquad\text{for all }\varphi\in E'.$$
--
--   Here $E'$ is the continuous dual of $E$ and $|\mu|$ is the total variation of $\mu$. The weak integral $\varphi\mapsto\int_X\varphi(f(x))\,d\mu(x)$ of $f$ a priori lies only in the weak completion $(E')^*$ of $E$ (the algebraic dual of $E'$); the theorem says that it is represented by a vector of $E$. This is the criterion that makes contour integrals $\int_\Gamma f(\xi)\,d\xi$ of continuous functions with values in a quasi-complete space (for the complex measure $d\xi$ on a curve) elements of $E$, the basis of vector-valued Cauchy theory.
--
--   **Formalization Note.** `HasComplexPettisIntegral μ f a` is the notion of `Def_PettisIntegral_ComplexMeasure`. "finite complex Radon measure" is `(μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]` on a locally compact Hausdorff space with its Borel $\sigma$-algebra: the total variation $|\mu|$ (`μ.variation`) is a finite regular Borel measure (a complex Borel measure is Radon if and only if its total variation is). "Quasi-complete Hausdorff locally convex space" is `[UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E]`. The positive-measure form is the published `PettisIntegral.pettisIntegrable_of_continuous_of_hasCompactSupport`; the source states the theorem for complex measures.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 713, Theorem C.4.3.5; classical reference: A. Grothendieck, Sur certains espaces de fonctions holomorphes. I, J. reine angew. Math. 192 (1953), pp. 35-64, Lemme 2 (as cited by the paper)

import Mathlib
import Definitions.Def_PettisIntegral_Basic
import Definitions.Def_PettisIntegral_ComplexMeasure

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- Pettis' integrability criterion for a finite complex Radon measure: a continuous compactly
supported function on a locally compact Hausdorff space with values in a quasi-complete Hausdorff
locally convex space has a Pettis integral. -/
theorem exists_hasComplexPettisIntegral_of_continuous_of_hasCompactSupport {E X : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → E) (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ a : E, HasComplexPettisIntegral μ f a := by sorry

end PettisIntegral
