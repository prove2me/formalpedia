-- Prove2me | Theorems.Thm_WhittEfficiency_MMs_proposition_3_1
-- name    : WhittEfficiency.MMs.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:18.003933+00:00
-- url     : https://prove2.me/theorems/50d257b4-7edc-46a1-971f-52a7a18f7d12
-- title:
--   Proposition 3.1, p. 720 — conditional tail and mean under the utilization equation
-- statement:
--   Let $s\geq1$ be an integer and consider a stable, steady-state $M/M/s$ queue with arrival rate $0<\lambda<s$, unit service rate at each server, and stationary probabilities $(p_n)$. Let $W$ be the FCFS waiting time of an arriving customer, $\rho=\lambda/s$, and suppose the utilization equation $(1-\rho)\sqrt{s}=\gamma$ holds. A positive wait has positive probability, and for every $x\geq0$,
--
--   $$
--   \mathbb P(W>x\mid W>0)=e^{-\gamma\sqrt{s}\,x},\qquad
--   \mathbb E[W\mid W>0]=\frac1{\gamma\sqrt{s}}.
--   $$
--
--   These formulas give both the conditional tail and conditional mean of the delay under the paper's utilization scaling.
--
--   **Formalization Note** The stationary birth–death law uses unit service rate, and the waiting-time law is the Erlang mixture in `WhittEfficiency.MMs.WaitLaw`. The printed (16) omits $x$ in the exponent and the printed (17) has $\sqrt2$ in place of $\sqrt{s}$; both are corrected here using the preceding and following text on pp. 719–720. The positive-delay conclusion guards the conditional probabilities and means against division by zero.
-- source:
--   Whitt, Understanding the efficiency of multi-server service systems, Management Sci. 38 (1992), p. 720, Proposition 3.1, (16)–(17), with (1) p. 708 and (3) p. 710; https://doi.org/10.1287/mnsc.38.5.708

import Mathlib
import Definitions.Def_WhittEfficiency_MMs_WaitLaw

open MeasureTheory ProbabilityTheory

namespace WhittEfficiency.MMs

/-- Whitt (1992), Proposition 3.1, p. 720, (16)–(17), with the printed omissions
corrected: the exponent in (16) includes `x`, and the denominator in (17) is `γ√s`. -/
theorem proposition_3_1
    (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) (hρ : lam < s)
    (p : ℕ → ℝ)
    (hp : QueueingFundamentals.BirthDeath.IsSteadyState
      (fun _ => lam) (QueueingFundamentals.BirthDeath.mmcDeath 1 s) p)
    (γ : ℝ) (h1 : (1 - lam / (s : ℝ)) * Real.sqrt s = γ) :
    0 < (waitLaw s p).real (Set.Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 ≤ x →
        (waitLaw s p).real (Set.Ioi x) /
          (waitLaw s p).real (Set.Ioi (0 : ℝ)) =
            Real.exp (-(γ * Real.sqrt s * x))) ∧
      (∫ w in Set.Ioi (0 : ℝ), w ∂(waitLaw s p)) /
        (waitLaw s p).real (Set.Ioi (0 : ℝ)) = 1 / (γ * Real.sqrt s) := by sorry

end WhittEfficiency.MMs
