-- Prove2me | Theorems.Thm_SupportVectorMachines_Concentration_theorem_6_13_banach_space_concentration_v2
-- name    : SupportVectorMachines.Concentration.theorem_6_13_banach_space_concentration_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:53.159795+00:00
-- url     : https://prove2.me/theorems/b668f30d-2b96-48a0-bb04-0c82060e0e76
-- title:
--   A general concentration inequality in separable Banach spaces (finite exponential moments)
-- statement:
--   This is Theorem 6.13 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 214), the tool from which Theorem 6.14 (Bernstein's inequality in Hilbert spaces) is derived.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $E$ a separable Banach space, and $\xi_1,\dots,\xi_n : \Omega \to E$ independent, $E$-valued, $P$-integrable random variables. Then, for all $\varepsilon > 0$ and all $t \ge 0$,
--   $$
--   P\Big(\Big\|\sum_{i=1}^n \xi_i\Big\| \ge \varepsilon n\Big) \le \exp\Big(-t\varepsilon n + t\,\mathbb E\Big\|\sum_{i=1}^n \xi_i\Big\| + \sum_{i=1}^n \mathbb E\big(e^{t\|\xi_i\|} - 1 - t\|\xi_i\|\big)\Big),
--   $$
--   where the expectations $\mathbb E(e^{t\|\xi_i\|} - 1 - t\|\xi_i\|) \in [0,\infty]$ are assumed finite.
--
--   **Formalization Note.** The retired version wrote the exponential-moment term as a real-valued Bochner integral, which equals the junk value $0$ (instead of $+\infty$) when $e^{t\|\xi_i\|}$ is not integrable, turning the book's vacuous case into a false bound (the accepted disproof: a geometric variable with $\mathbb E e^{3\xi} = \infty$). The corrected statement adds the hypothesis `hexp` that $e^{t\|\xi_i\|}$ is $P$-integrable for every $i$: in the book the right-hand side is $+\infty$ and the inequality trivially true otherwise, so no instance of the printed statement is lost, and under `hexp` every integral is a genuine expectation. $P$-integrability of the $\xi_i$ (`hint`), measurability, independence (`iIndepFun`) and the separable Banach space are as in the book; the probability is `P.real` of the event $\{\|\sum_i \xi_i\| \ge \varepsilon n\}$.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 214, Theorem 6.13

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Concentration

/-- Theorem 6.13, Steinwart & Christmann, *Support Vector Machines*, Springer 2008, p. 214: let
`(Ω, A, P)` be a probability space, `E` be a separable Banach space, and `ξ₁,…,ξₙ : Ω → E` be
independent, `E`-valued, `P`-integrable random variables. Then, for all `ε > 0` and all `t ≥ 0`,
`P(‖∑ᵢ ξᵢ‖ ≥ εn) ≤ exp(-tεn + t·E‖∑ᵢ ξᵢ‖ + ∑ᵢ E(e^{t‖ξᵢ‖} - 1 - t‖ξᵢ‖))`.
The exponential moments `E e^{t‖ξᵢ‖} ∈ [0,∞]` are assumed finite (`hexp`): when one of them is
`+∞` the book's right-hand side reads `+∞` and the inequality holds vacuously, so no instance of
the printed statement is lost.
Corrected version of `theorem_6_13_banach_space_concentration`, whose exponential-moment term was
a real-valued Bochner integral, equal to the junk value `0` (instead of `+∞`) for a
non-integrable `e^{t‖ξᵢ‖}`, which made the bound false. -/
theorem theorem_6_13_banach_space_concentration_v2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E]
    (n : ℕ)
    (ξ : Fin n → Ω → E) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hint : ∀ i, Integrable (ξ i) P) (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : 0 ≤ t)
    (hexp : ∀ i, Integrable (fun ω => Real.exp (t * ‖ξ i ω‖)) P) :
    P.real {ω | ε * n ≤ ‖∑ i, ξ i ω‖} ≤
      Real.exp (-t * ε * n + t * (∫ ω, ‖∑ i, ξ i ω‖ ∂P) +
        ∑ i, ∫ ω, (Real.exp (t * ‖ξ i ω‖) - 1 - t * ‖ξ i ω‖) ∂P) := by sorry

end SupportVectorMachines.Concentration
