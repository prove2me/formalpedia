-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_Q_unique_optimum
-- name    : StrategicRFx.Benefit.Q_unique_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:05.746995+00:00
-- url     : https://prove2.me/theorems/7d0efeb5-a792-44d1-ba4e-ea47a573befa
-- title:
--   Proof of Theorem 5, p. ec21 — (π^F_1, π^F_2) is the unique optimal solution to [Q]
-- statement:
--   Let $\pi^F=(\pi^F_1,\pi^F_2)$ solve $\pi_i=\theta_i(\Pi-\pi_j-\Pi^{-i})^+$ for $\{i,j\}=\{1,2\}$, and consider the program
--   $$[Q]\qquad \min_{\pi_1,\pi_2}\ \Pi-\pi_1-\pi_2\quad\text{s.t. } \pi_i\le\theta_i\big(\Pi-\pi_j-\Pi^{-i}\big)^+\ (\{i,j\}=\{1,2\}),\ \ \pi_1,\pi_2\ge 0.$$
--   Then $\pi^F$ is feasible for [Q], every feasible $\pi$ satisfies $\Pi-\pi^F_1-\pi^F_2\le\Pi-\pi_1-\pi_2$, and a feasible $\pi$ attains this value only if $\pi=\pi^F$.
--
--   By Lemma 2 the feasible set of [Q] is exactly the set of offer pairs the buyer accepts, so this step converts the RFx analysis into the comparison of Theorem 5.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), proof of Theorem 5, p. ec21, "We now show that (π^F_1, π^F_2) is the unique optimal solution to [Q]."

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

namespace StrategicRFx.Benefit

/-- Proof of Theorem 5 (p. ec21): `(π^F_1, π^F_2)` is the unique optimal solution of
`[Q] min Π - π_1 - π_2 s.t. π_i ≤ θ_i (Π - π_j - Π^{-i})^+, π_1, π_2 ≥ 0`. -/
theorem Q_unique_optimum (P : Params) (hP : Standing P) (πF : Fin 2 → ℝ)
    (hF : ∀ i, πF i = P.θ i * max (P.Pi - πF (other i) - P.PiEx i) 0) :
    QFeasible P πF ∧
      ∀ π : Fin 2 → ℝ, QFeasible P π →
        P.Pi - πF 0 - πF 1 ≤ P.Pi - π 0 - π 1 ∧
          (P.Pi - π 0 - π 1 = P.Pi - πF 0 - πF 1 → π = πF) := by sorry

end StrategicRFx.Benefit
