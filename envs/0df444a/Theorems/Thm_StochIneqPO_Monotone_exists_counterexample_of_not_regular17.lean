-- Prove2me | Theorems.Thm_StochIneqPO_Monotone_exists_counterexample_of_not_regular17
-- name    : StochIneqPO.Monotone.exists_counterexample_of_not_regular17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:27:55.488526+00:00
-- url     : https://prove2.me/theorems/7f3d6a85-38ae-4ad6-a8f1-69c37664de80
-- title:
--   Proof of Theorem 6, p. 909 — if (17) fails, some nondecreasing sequence converges in probability but not almost surely
-- statement:
--   Let $E$ be a complete separable metric space with a closed partial ordering $\le$ and its Borel $\sigma$-algebra, and suppose that $E$ does **not** satisfy condition (17). Then there exist a probability space $(\Omega,\mathcal F,\mu)$ and measurable maps $X_1,X_2,\dots:\Omega\to E$ with $X_1(\omega)\le X_2(\omega)\le\cdots$ for every $\omega$, such that
--
--   1. $(X_n)$ converges in probability to a constant: there is $z\in E$ with $\mu\{\omega : d(X_n(\omega),z)\ge\varepsilon\}\to0$ for every $\varepsilon>0$;
--   2. $(X_n)$ does not converge almost surely: there is no $Y:\Omega\to E$ with $X_n(\omega)\to Y(\omega)$ for $\mu$-almost every $\omega$.
--
--   This is the "only if" half of the second part of Theorem 6: without (17), almost sure convergence is not equivalent to the other three modes for all nondecreasing sequences.
--
--   **Formalization Note** The paper says "take any probability space" carrying events $C_i$ with $\mu(C_i)\to0$ and $\mu(C_i \text{ infinitely often})=1$; such events do not exist on every probability space (e.g. a one-point space), so the statement asserts the existence of a suitable probability space, which is what the argument establishes. The probability space is taken in Lean's lowest universe `Type`.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Proof of Theorem 6, failure of (17), p. 909 (PDF p. 11)

import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_ConvergenceModes

namespace StochIneqPO.Monotone

open MeasureTheory Filter

theorem exists_counterexample_of_not_regular17 {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    (h17 : ¬ Regular17 E) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ X : ℕ → Ω → E, (∀ i, Measurable (X i)) ∧ (∀ ω, Monotone fun i => X i ω) ∧
        (∃ z : E, TendstoInMeasure μ X atTop (fun _ => z)) ∧ ¬ ConvergesAS μ X := by sorry

end StochIneqPO.Monotone
