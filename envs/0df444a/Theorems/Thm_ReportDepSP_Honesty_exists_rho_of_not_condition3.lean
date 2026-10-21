-- Prove2me | Theorems.Thm_ReportDepSP_Honesty_exists_rho_of_not_condition3
-- name    : ReportDepSP.Honesty.exists_rho_of_not_condition3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:56.93315+00:00
-- url     : https://prove2.me/theorems/3104be98-478f-4177-81f6-7fcf913934b5
-- title:
--   Proof of Proposition 2, p. 13 — if (3) fails at some r̄, some strictly decreasing ρ makes R̃ strictly better than the truth
-- statement:
--   Let $P$ be any weight function on attainability states, $\widetilde R$ any ROL, and $v$ any payoff vector. Suppose condition (3) is violated at some $\bar r \in ⟦1,n⟧$:
--   $$\Delta_{\bar r} = \sum_{r=1}^{\bar r}\bigl(f_r - \widetilde f_r\bigr) < 0 .$$
--   Then there is a strictly decreasing report-dependent payoff $\rho:⟦1,n⟧\to\mathbb R$ such that
--   $$U(v\mid R) \ <\ U(v\mid \widetilde R).$$
--
--   This is the "only if" direction of Proposition 2: a list that raises the probability of a top-$\bar r$ match beats the truth once the report-dependent payoff rewards ranks $1,\dots,\bar r$ strongly enough.
--
--   **Formalization Note** The paper describes $\rho$ as a limit of decreasing functions with $\rho(r)\to\rho(1)$ for $r\le\bar r$ and $\rho(r)\to 0$ for $r>\bar r$; the statement asks for an actual strictly decreasing $\rho$, which is what Proposition 2 needs. No hypothesis on $P$ or $v$ is imposed (the statement is stronger without them). Ranks are 0-indexed `Fin n`, `Iic rbar` is the page's $1,\dots,\bar r$.
-- source:
--   Meisner, Report-dependent utility and strategy-proofness, CRC TRR 190 Discussion Paper No. 289 (2021; Management Science doi:10.1287/mnsc.2022.4504), proof of Proposition 2 (Appendix), second paragraph, p. 13

import Mathlib
import Definitions.Def_ReportDepSP_Honesty_Setting

namespace ReportDepSP.Honesty

open Finset

/-- Proof of Proposition 2 (p. 13), "only if": if condition (3) fails at some `r̄` for the ROL
`Rt`, there is a strictly decreasing `ρ` with `U(v|R) < U(v|R̃)`. -/
theorem exists_rho_of_not_condition3 {n : ℕ} (P : (Fin n → Bool) → ℝ) (Rt : Equiv.Perm (Fin n))
    (v : Fin n → ℝ) (rbar : Fin n)
    (hviol : ∑ r ∈ Iic rbar, (matchProb P 1 r - matchProb P Rt r) < 0) :
    ∃ ρ : Fin n → ℝ, StrictAnti ρ ∧ payoff v ρ P 1 < payoff v ρ P Rt := by sorry

end ReportDepSP.Honesty
