-- Prove2me | Theorems.Thm_PettisIntegral_HasPettisIntegral_seminorm_le_lintegral
-- name    : PettisIntegral.HasPettisIntegral.seminorm_le_lintegral
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:38.756453+00:00
-- url     : https://prove2.me/theorems/1eaaf801-c3ee-4a43-b552-97d7bbf6787d
-- title:
--   Lemma C.4.3.9 — seminorm estimate for Pettis integrals: $\nu\bigl(\int_X f\,d\mu\bigr)\le\int_X\nu(f(x))\,d\mu(x)$
-- statement:
--   **Seminorm estimate for Pettis integrals (Lemma C.4.3.9).** Let $E$ be a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$, let $(X,\mu)$ be a measure space with $\mu$ a positive measure, and let $f\colon X\to E$ be $\mu$-integrable in the sense of Pettis, with integral $\int_X f\,d\mu\in E$. Then for every continuous seminorm $\nu$ on $E$ such that $x\mapsto\nu(f(x))$ is $\mu$-measurable,
--   $$\nu\Bigl(\int_X f\,d\mu\Bigr)\ \le\ \int_X\nu(f(x))\,d\mu(x).$$
--   The right-hand side is the integral of a non-negative measurable function and may be $+\infty$.
--
--   This is the triangle inequality for vector-valued integrals. It is the tool for all continuity statements about Pettis integrals (for instance the convergence of integrals of uniformly convergent nets, and the boundedness of operators defined by integrals), since the topology of $E$ is defined by its continuous seminorms.
--
--   **Deviation from the source.** The source states the inequality for a finite complex Radon measure $\mu$, in which case the right-hand side of the printed inequality is a complex number and the inequality has no meaning as printed. The statement here is the classical one, for a positive measure.
--
--   **Formalization Note.** `HasPettisIntegral 𝕜 μ f a` (from `Def_PettisIntegral_Basic`) says that $a$ is the Pettis integral of $f$. The inequality is stated in $[0,\infty]$ with the lower Lebesgue integral: `ENNReal.ofReal (p a) ≤ ∫⁻ x, ENNReal.ofReal (p (f x)) ∂μ`, so that an infinite right-hand side is allowed, as in Remark C.4.3.10 of the source. "$\mu$-measurable" is `AEMeasurable`. "Hausdorff locally convex" is `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]`. The statement does not involve a topology on $X$ and is given for an arbitrary measure space (the source: $X$ locally compact Hausdorff, $\mu$ finite Radon, $\mathbb k=\mathbb C$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 715, Lemma C.4.3.9 and Remark C.4.3.10; classical reference: a variant is given in N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. VI, §1, no. 2, Prop. 6 (as cited by the paper)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- A continuous seminorm of a Pettis integral is at most the integral of the seminorm. -/
theorem HasPettisIntegral.seminorm_le_lintegral {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [MeasurableSpace X] {μ : Measure X} {f : X → E} {a : E}
    (ha : HasPettisIntegral 𝕜 μ f a) (p : Seminorm 𝕜 E) (hp : Continuous p)
    (hpf : AEMeasurable (fun x => p (f x)) μ) :
    ENNReal.ofReal (p a) ≤ ∫⁻ x, ENNReal.ofReal (p (f x)) ∂μ := by sorry

end PettisIntegral
