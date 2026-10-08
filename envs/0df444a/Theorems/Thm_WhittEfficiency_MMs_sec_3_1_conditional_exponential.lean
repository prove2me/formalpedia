-- Prove2me | Theorems.Thm_WhittEfficiency_MMs_sec_3_1_conditional_exponential
-- name    : WhittEfficiency.MMs.sec_3_1_conditional_exponential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:12.263369+00:00
-- url     : https://prove2.me/theorems/c065891e-46ab-43bb-aaf0-1be39f6a6b8e
-- title:
--   §3.1, p. 719 — conditional M/M/s waiting time is exponential
-- statement:
--   Let $s\geq1$ be an integer and consider a stable, steady-state $M/M/s$ queue with arrival rate $0<\lambda<s$, unit service rate at each server, and stationary probabilities $(p_n)$. Put $\rho=\lambda/s$, and let $W$ be the FCFS waiting time of an arriving customer. Then a positive wait has positive probability and
--
--   $$
--   \mathcal L(W\mid W>0)=\operatorname{Exp}\bigl(s(1-\rho)\bigr).
--   $$
--
--   Thus the waiting time of a delayed customer has mean $1/[s(1-\rho)]$. This identifies the conditional distribution needed for Proposition 3.1.
--
--   **Formalization Note** The waiting-time law is the Erlang mixture defined in `WhittEfficiency.MMs.WaitLaw`. The conclusion is equality of the restriction of that measure to $(0,\infty)$ with its positive-wait mass times the exponential measure.
-- source:
--   Whitt, Understanding the efficiency of multi-server service systems, Management Sci. 38 (1992), p. 719, §3.1, sentence immediately preceding Proposition 3.1; https://doi.org/10.1287/mnsc.38.5.708

import Mathlib
import Definitions.Def_WhittEfficiency_MMs_WaitLaw

open MeasureTheory ProbabilityTheory

namespace WhittEfficiency.MMs

/-- Whitt (1992), §3.1, p. 719: conditional on a positive wait, the M/M/s wait
is exponential with mean `1 / (s * (1 - ρ))`. -/
theorem sec_3_1_conditional_exponential
    (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) (hρ : lam < s)
    (p : ℕ → ℝ)
    (hp : QueueingFundamentals.BirthDeath.IsSteadyState
      (fun _ => lam) (QueueingFundamentals.BirthDeath.mmcDeath 1 s) p) :
    0 < (waitLaw s p).real (Set.Ioi (0 : ℝ)) ∧
      (waitLaw s p).restrict (Set.Ioi (0 : ℝ)) =
        (waitLaw s p) (Set.Ioi (0 : ℝ)) •
          expMeasure ((s : ℝ) * (1 - lam / (s : ℝ))) := by sorry

end WhittEfficiency.MMs
