-- Prove2me | Theorems.Thm_StochIneqPO_Monotone_ae_tendsto_of_regular17
-- name    : StochIneqPO.Monotone.ae_tendsto_of_regular17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:27:55.531502+00:00
-- url     : https://prove2.me/theorems/756c0407-d49a-4bed-9e9c-9b234944a3be
-- title:
--   Proof of Theorem 6, pp. 908–909 — under (17), convergence in probability of a nondecreasing sequence is almost sure
-- statement:
--   Let $E$ be a complete separable metric space with a closed partial ordering $\le$ and its Borel $\sigma$-algebra, and assume that $E$ satisfies condition (17): whenever $x_n\le y_n\le x_{n+1}$ for all $n$ and $x_n\to z$, also $y_n\to z$. Let $(\Omega,\mathcal F,\mu)$ be a probability space and $X_1,X_2,\dots:\Omega\to E$ measurable with $X_1(\omega)\le X_2(\omega)\le\cdots$ for every $\omega$. If $X_i\to Y$ in probability for a measurable $Y:\Omega\to E$, then
--
--   $$
--   X_i(\omega)\;\longrightarrow\;Y(\omega)\qquad\text{for }\mu\text{-almost every }\omega .
--   $$
--
--   This is the implication (iii) $\Rightarrow$ (iv) under (17), the "if" half of the second part of Theorem 6; it identifies the almost sure limit with the limit in probability.
--
--   **Formalization Note** Same conventions as the other statements of the mission: `OrderClosedTopology` for the closed ordering, second countability for separability, pointwise monotonicity, sequences indexed from $0$.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Proof of Theorem 6, (iii) and (17) ⇒ (iv), pp. 908–909 (PDF pp. 10–11)

import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_ConvergenceModes

namespace StochIneqPO.Monotone

open MeasureTheory Filter Topology

theorem ae_tendsto_of_regular17 {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    (h17 : Regular17 E)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i)) (hmono : ∀ ω, Monotone fun i => X i ω)
    (Y : Ω → E) (hY : Measurable Y) (hXY : TendstoInMeasure μ X atTop Y) :
    ∀ᵐ ω ∂μ, Tendsto (fun i => X i ω) atTop (𝓝 (Y ω)) := by sorry

end StochIneqPO.Monotone
