-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_lemma_1
-- name    : StrategicRFx.Benefit.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:01.55489+00:00
-- url     : https://prove2.me/theorems/3f5fd014-13a0-4bd4-8343-acf85e1870c1
-- title:
--   Lemma 1, p. 17 — if the buyer rejects j's offer, the contract is π_j = θ_j(Π − π_i − π^{-j}_0), or j is excluded
-- statement:
--   Fix supplier $j$, supplier $i$'s profit $\pi_i$ and the buyer's single-sourcing profit $\pi_0^{-j}$, and suppose the buyer rejects supplier $j$'s offer, so that she and supplier $j$ solve the Nash bargaining program
--   $$\max_{\pi_j}\ \pi_j^{\theta_j}\,\big(\Pi-\pi_i-\pi_j-\pi_0^{-j}\big)^{1-\theta_j}\quad\text{s.t. } \pi_j\ge 0,\ \ \Pi-\pi_i-\pi_j\ge\pi_0^{-j}.$$
--
--   1. If $\Pi-\pi_i-\pi_0^{-j}\ge 0$, the program has exactly one solution,
--   $$\pi_j(\pi_i,\pi_0^{-j})=\theta_j\big(\Pi-\pi_i-\pi_0^{-j}\big),$$
--   and the buyer's profit is $\pi_0=\Pi-\pi_i-\pi_j=(1-\theta_j)(\Pi-\pi_i)+\theta_j\pi_0^{-j}$.
--   2. If $\Pi-\pi_i-\pi_0^{-j}<0$, the program has no solution: supplier $j$ is excluded.
--
--   The closed form is the building block of every later step: it enters the buyer's profit in the leader program [RFx-i] and the fixed-point characterization of the most favorable bargaining outcome.
--
--   **Formalization Note** The standing hypotheses of the model are assumed although only $0<\theta_j<1$ is relevant here. "Excludes supplier $j$" is read as infeasibility of the program.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Lemma 1, p. 17 (proof p. ec7)

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

namespace StrategicRFx.Benefit

/-- Lemma 1 (p. 17). If the buyer rejects supplier `j`'s offer, then given `(π_i, π_0^{-j})`
with `Π - π_i - π_0^{-j} ≥ 0` the follower program has the unique solution
`π_j = θ_j (Π - π_i - π_0^{-j})`, and the buyer gets `π_0 = (1 - θ_j)(Π - π_i) + θ_j π_0^{-j}`;
otherwise the program is infeasible ("excludes supplier `j`"). -/
theorem lemma_1 (P : Params) (hP : Standing P) (j : Fin 2) (πi π' : ℝ) :
    (0 ≤ P.Pi - πi - π' →
      (∀ x, IsFollowerSolution P j πi π' x ↔ x = followerSplit P j πi π') ∧
        P.Pi - πi - followerSplit P j πi π' = (1 - P.θ j) * (P.Pi - πi) + P.θ j * π') ∧
    (P.Pi - πi - π' < 0 → ∀ x, ¬ IsFollowerSolution P j πi π' x) := by sorry

end StrategicRFx.Benefit
