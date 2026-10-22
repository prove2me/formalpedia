-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_proposition_1
-- name    : StrategicRFx.Benefit.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:05.748001+00:00
-- url     : https://prove2.me/theorems/e2b93939-3935-4632-8892-62453686239d
-- title:
--   Proposition 1, p. 12 — the buyer's maximum dual-sourcing equilibrium profit is Π − π^F_1 − π^F_2
-- statement:
--   Under simultaneous bilateral bargaining without an RFx stage, consider the system
--   $$\pi_i=\theta_i\big(\Pi-\pi_j-\Pi^{-i}\big)^+,\qquad \{i,j\}=\{1,2\}.$$
--   It has a unique solution $\pi^F=(\pi^F_1,\pi^F_2)$, the **most favorable bargaining outcome**, and the buyer's maximum profit among all dual-sourcing equilibria $(\pi_1,\pi_2,\pi_1^{-2},\pi_2^{-1})$ of [Simu-1], [Simu-2] is
--   $$\Pi-\pi^F_1-\pi^F_2 ,$$
--   the maximum being attained by some equilibrium.
--
--   This is the benchmark of the paper: Theorem 5 compares the buyer's profit after an RFx stage with it.
--
--   **Formalization Note** The maximum is stated as `IsGreatest` of the set of buyer profits over all dual-sourcing equilibria (membership and upper bound), not as a real supremum. An equilibrium requires $\pi_k^{-l}\ge 0$ (Assumption 3) and that each $\pi_i$ maximize the [Simu-i] Nash product over its feasible set; the free variable $\pi_i^{-j}$ of [Simu-i] is not constrained further.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Proposition 1, p. 12 (proof pp. ec5–ec6)

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

namespace StrategicRFx.Benefit

/-- Proposition 1 (p. 12). The system `π_i = θ_i (Π - π_j - Π^{-i})^+` (`{i, j} = {1, 2}`) has a
unique solution `π^F`, and `Π - π^F_1 - π^F_2` is the buyer's maximum profit among all
dual-sourcing equilibria of simultaneous bargaining (attained). -/
theorem proposition_1 (P : Params) (hP : Standing P) :
    (∃! πF : Fin 2 → ℝ, ∀ i, πF i = P.θ i * max (P.Pi - πF (other i) - P.PiEx i) 0) ∧
    ∀ πF : Fin 2 → ℝ, (∀ i, πF i = P.θ i * max (P.Pi - πF (other i) - P.PiEx i) 0) →
      IsGreatest {v : ℝ | ∃ π πex : Fin 2 → ℝ, IsSimuEquilibrium P π πex ∧ v = P.Pi - π 0 - π 1}
        (P.Pi - πF 0 - πF 1) := by sorry

end StrategicRFx.Benefit
