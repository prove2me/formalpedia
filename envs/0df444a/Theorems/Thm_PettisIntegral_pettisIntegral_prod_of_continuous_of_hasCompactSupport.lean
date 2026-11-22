-- Prove2me | Theorems.Thm_PettisIntegral_pettisIntegral_prod_of_continuous_of_hasCompactSupport
-- name    : PettisIntegral.pettisIntegral_prod_of_continuous_of_hasCompactSupport
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:49.628438+00:00
-- url     : https://prove2.me/theorems/fe53225c-bd16-4a4b-a642-2cfcf17958ab
-- title:
--   Remark C.4.4.2 — Fubini's theorem for continuous compactly supported functions with values in a quasi-complete locally convex space
-- statement:
--   **Fubini's theorem for continuous compactly supported vector-valued functions (Remark C.4.4.2).** Let $E$ be a quasi-complete Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$. Let $X$ and $Y$ be locally compact Hausdorff $\sigma$-compact spaces with positive Radon measures $\mu$ and $\nu$, and let $f\colon X\times Y\to E$ be continuous with compact support. Then, all integrals being integrals in the sense of Pettis (vectors of $E$):
--
--   1. for every $x\in X$ the function $f(x,\cdot)$ is $\nu$-integrable, and for every $y\in Y$ the function $f(\cdot,y)$ is $\mu$-integrable;
--   2. $f$ is $(\mu\otimes\nu)$-integrable;
--   3. the partial integrals $x\mapsto\int_Y f(x,y)\,d\nu(y)$ and $y\mapsto\int_X f(x,y)\,d\mu(x)$ are $\mu$-integrable and $\nu$-integrable respectively;
--   4. the three integrals agree in $E$:
--   $$\int_X\Bigl(\int_Y f(x,y)\,d\nu(y)\Bigr)d\mu(x)\;=\;\int_{X\times Y}f\,d(\mu\otimes\nu)\;=\;\int_Y\Bigl(\int_X f(x,y)\,d\mu(x)\Bigr)d\nu(y).$$
--
--   For a general weakly integrable $f$ the Fubini theorem for the Pettis integral (Lemma C.4.4.1 of the paper) needs the integrability of all partial functions as a hypothesis and only gives an identity in the weak completion $(E')^*$; for continuous compactly supported functions with values in a quasi-complete space everything is automatic, because the closed absolutely convex hull of the compact set $f(X\times Y)$ is compact. This is the form used for convolutions and for Weil's integral formula with vector-valued test functions.
--
--   **Formalization Note.** `PettisIntegrable 𝕜 μ g` and `pettisIntegral 𝕜 μ g` are the notions of `Def_PettisIntegral_Basic` (the Pettis integral is unique because $E$ is Hausdorff and locally convex). "quasi-complete Hausdorff locally convex space" is `[UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E]` (the topology is defined by a family of seminorms; closed von Neumann bounded sets are complete). "Positive Radon measure" is `[μ.Regular]` on the Borel $\sigma$-algebra (`[BorelSpace X]`); the measures need not be finite. The product measure is Mathlib's `μ.prod ν` on the product $\sigma$-algebra; $\sigma$-compactness (`[SigmaCompactSpace X]`, as in Lemma C.4.4.1 of the source) makes $\mu$ and $\nu$ $\sigma$-finite. The product $\sigma$-algebra can be smaller than the Borel $\sigma$-algebra of $X\times Y$ when the spaces are not second countable, but a continuous compactly supported scalar function on $X\times Y$ is measurable for it (Mathlib: `HasCompactSupport.stronglyMeasurable_of_prod`), so the weak integral of $f$ for `μ.prod ν` is the integral for the Radon product measure. The conclusion is one conjunction: integrability of all partial functions, of $f$, and of the two functions of partial integrals, and the two equalities with `pettisIntegral 𝕜 (μ.prod ν) f`. The source assumes the measures complete; with almost everywhere measurability (`AEMeasurable`) this is not needed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 717, Remark C.4.4.2 (with Lemma C.4.4.1); classical reference: N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. III, §4, p. III.43, Remark, and Ch. III, §3, Prop. 7 (as cited by the paper)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- Fubini's theorem for continuous compactly supported functions with values in a quasi-complete
Hausdorff locally convex space: the function is Pettis integrable for the product measure, its
partial Pettis integrals exist and are Pettis integrable, and the three integrals agree. -/
theorem pettisIntegral_prod_of_continuous_of_hasCompactSupport {𝕜 E X Y : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [SigmaCompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [μ.Regular] (ν : Measure Y) [ν.Regular]
    (f : X × Y → E) (hf : Continuous f) (hc : HasCompactSupport f) :
    (∀ x : X, PettisIntegrable 𝕜 ν (fun y => f (x, y))) ∧
    (∀ y : Y, PettisIntegrable 𝕜 μ (fun x => f (x, y))) ∧
    PettisIntegrable 𝕜 (μ.prod ν) f ∧
    PettisIntegrable 𝕜 μ (fun x => pettisIntegral 𝕜 ν (fun y => f (x, y))) ∧
    PettisIntegrable 𝕜 ν (fun y => pettisIntegral 𝕜 μ (fun x => f (x, y))) ∧
    pettisIntegral 𝕜 μ (fun x => pettisIntegral 𝕜 ν (fun y => f (x, y))) =
      pettisIntegral 𝕜 (μ.prod ν) f ∧
    pettisIntegral 𝕜 ν (fun y => pettisIntegral 𝕜 μ (fun x => f (x, y))) =
      pettisIntegral 𝕜 (μ.prod ν) f := by sorry

end PettisIntegral
