-- Prove2me | Theorems.Thm_PettisIntegral_tendsto_pettisIntegral_of_tendstoUniformly
-- name    : PettisIntegral.tendsto_pettisIntegral_of_tendstoUniformly
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:30.195995+00:00
-- url     : https://prove2.me/theorems/ef4f3bd1-8bf1-4010-ad6a-4380592cc433
-- title:
--   Lemma C.4.3.12 — the Pettis integrals of a uniformly convergent net of continuous functions converge to the integral of the limit
-- statement:
--   **Continuity of the Pettis integral under uniform convergence (Lemma C.4.3.12).** Let $E$ be a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$, $X$ a locally compact Hausdorff space and $\mu$ a finite positive Radon measure on $X$. Let $I$ be a directed set and $(f_i)_{i\in I}$ a net of continuous functions $f_i\colon X\to E$, each $\mu$-integrable in the sense of Pettis, which converges uniformly on $X$ to a continuous function $f\colon X\to E$ that is also $\mu$-integrable in the sense of Pettis. Then
--   $$\lim_{i\in I}\int_X f_i\,d\mu=\int_X f\,d\mu\qquad\text{in }E.$$
--
--   Uniform convergence means: for every continuous seminorm $\nu$ on $E$, $\lim_{i\in I}\sup_{x\in X}\nu(f_i(x)-f(x))=0$. This is the paper's continuity criterion for vector-valued integrals (§C.4.3.3).
--
--   **Deviation from the source.** The source allows a finite complex Radon measure; the statement is given for a finite positive Radon measure.
--
--   **Formalization Note.** `PettisIntegrable` and `pettisIntegral` are from `Def_PettisIntegral_Basic`. The net is a family indexed by a non-empty directed preorder `ι`, and limits are taken along `Filter.atTop`. Uniform convergence is Mathlib's `TendstoUniformly` for the uniform structure of the topological vector space $E$ (`[UniformSpace E] [IsUniformAddGroup E]`), which is uniform convergence for every continuous seminorm. "Finite positive Radon measure" is `[IsFiniteMeasure μ] [μ.Regular]` on the Borel $\sigma$-algebra; "Hausdorff locally convex" is `[ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 716, Lemma C.4.3.12, with the definition of uniform convergence in §C.4.3.3

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- If a net of continuous Pettis integrable functions converges uniformly to a continuous Pettis
integrable function, then the Pettis integrals against a finite positive Radon measure converge. -/
theorem tendsto_pettisIntegral_of_tendstoUniformly {𝕜 E X ι : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (F : ι → X → E) (f : X → E) (hF : ∀ i, Continuous (F i)) (hf : Continuous f)
    (hFi : ∀ i, PettisIntegrable 𝕜 μ (F i)) (hfi : PettisIntegrable 𝕜 μ f)
    (hlim : TendstoUniformly F f Filter.atTop) :
    Filter.Tendsto (fun i => pettisIntegral 𝕜 μ (F i)) Filter.atTop
      (nhds (pettisIntegral 𝕜 μ f)) := by sorry

end PettisIntegral
