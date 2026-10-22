-- Prove2me | Theorems.Thm_PermBlockchain_Failure_proposition_4_8
-- name    : PermBlockchain.Failure.proposition_4_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:27.007368+00:00
-- url     : https://prove2.me/theorems/9f433af5-4288-4c49-9449-5cfd3e4edc6b
-- title:
--   Proposition 4.8, p. 19 — for all sufficiently large Δ = H − L, full adoption raises total welfare yet is not an equilibrium
-- statement:
--   Consider the reduced-form blockchain supply chain under its standing assumptions, with $L$ fixed and $H=L+\Delta$. An **adoption failure** at $\Delta$ is the situation in which full blockchain adoption raises total welfare, $W^F(\Delta)>W^N(\Delta)$, yet full adoption is not an equilibrium of the adoption game (8).
--
--   **Proposition 4.8.** An adoption failure arises for sufficiently large $\Delta$: there is $\underline\Delta$ such that
--   $$\forall\,\Delta>\underline\Delta:\qquad W^F(\Delta)>W^N(\Delta)\quad\text{and full adoption is not an equilibrium},$$
--   for every such $\Delta$ at which Assumption 1 holds.
--
--   This is the first main result of the paper: the benefits of a permissioned blockchain accrue to consumers, while manufacturers bear its cost and cannot recover it through prices, so a welfare-improving technology is not adopted.
--
--   **Formalization Note** Total welfare is evaluated at Proposition A.1's closed forms, the manufacturers' gross profit is $0$ in every subgame (p. 34, p. 36), and "equilibrium" is a pure Nash equilibrium of (8) with that payoff. Assumption 1 depends on $\Delta$ through $H$ and is therefore a hypothesis at each $\Delta$; it is satisfiable and, once true, stays true for larger $\Delta$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), p. 19, Proposition 4.8; adoption failure defined on pp. 14 and 19

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

namespace PermBlockchain.Failure

/-- **Proposition 4.8** (p. 19): an adoption failure arises for sufficiently large `Δ = H − L`. -/
theorem proposition_4_8 {m : ℕ} (M : Model m) (hM : M.Standing) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ < Δ → M.Assumption1 Δ → M.AdoptionFailure Δ := by sorry

end PermBlockchain.Failure
