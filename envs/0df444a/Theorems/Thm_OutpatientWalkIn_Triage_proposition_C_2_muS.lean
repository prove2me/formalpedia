-- Prove2me | Theorems.Thm_OutpatientWalkIn_Triage_proposition_C_2_muS
-- name    : OutpatientWalkIn.Triage.proposition_C_2_muS
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:02.076989+00:00
-- url     : https://prove2.me/theorems/4d3cbbd7-2c13-4c7c-bc18-8708f089bcb8
-- title:
--   Proposition C.2 (µ_S-part), Online App. p. 8 — π(δ, µ_S) is continuous and strictly decreasing in the appointment capacity µ_S
-- statement:
--   Let $\lambda>0$ be the arrival rate of strategic patients and $\delta\ge0$ a delay threshold, and let $\pi(\delta,\mu_S)$ be the blocking probability of the M/D/1/K−1+p appointment queue with service rate $\mu_S$ (Corollary C.1), with $K=\lceil\delta\mu_S\rceil$ and $p=\delta\mu_S+1-K$. Then, on $\mu_S\in(0,\infty)$,
--   $$\mu_S\longmapsto\pi(\delta,\mu_S)\quad\text{is continuous and strictly decreasing.}$$
--
--   Adding appointment capacity both speeds up service and, at a fixed threshold, enlarges the effective buffer $\delta\mu_S$; both lower the fraction of patients who do not schedule. In Proposition 6 this monotonicity compares the triage model's balking at an allocation $\mu_S<\mu-\underline\mu_W$ with its balking at $\mu-\underline\mu_W$.
--
--   **Formalization Note** This item is the $\mu_S$ half of Proposition C.2; the $\delta$ half is not posed in this mission. Continuity includes the points where $\delta\mu_S$ is an integer, where $K$ jumps and $p$ passes from $1$ to values near $0$. The paper proves this half by a sample-path argument on the queue; here it is stated for the closed form of Corollary C.1.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix p. 8, Proposition C.2 (µ_S-part)

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting

namespace OutpatientWalkIn.Triage

theorem proposition_C_2_muS (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 ≤ δ) :
    StrictAntiOn (fun μS => blockProb lam δ μS) (Set.Ioi 0) ∧
      ContinuousOn (fun μS => blockProb lam δ μS) (Set.Ioi 0) := by sorry

end OutpatientWalkIn.Triage
