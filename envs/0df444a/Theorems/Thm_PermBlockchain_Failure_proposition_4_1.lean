-- Prove2me | Theorems.Thm_PermBlockchain_Failure_proposition_4_1
-- name    : PermBlockchain.Failure.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:50.148042+00:00
-- url     : https://prove2.me/theorems/e6af17b7-5277-4e51-b83a-ca7a1dd12889
-- title:
--   Proposition 4.1, pp. 15–16 — consumer welfare: $W^F_C \ge W^P_C > W^N_C$
-- statement:
--   Consider the reduced-form blockchain supply chain under its standing assumptions, with $H=L+\Delta$ for some $\Delta>0$, and suppose Assumption 1 holds at $\Delta$. The consumer welfare $W_C^X=\mathbb E[\max\{u^X,\varphi\}]$ in the full, partial and non-adoption scenarios satisfies
--   $$W^F_C\ \ge\ W^P_C\ >\ W^N_C .$$
--
--   Both forms of blockchain adoption therefore raise consumer welfare relative to non-adoption, and full adoption raises it at least as much as partial adoption. This is the consumer side of the welfare comparison behind Proposition 4.6.
--
--   **Formalization Note** $W_C^X$ is the Bochner integral of $\varphi\mapsto\max\{u^X,\varphi\}$ against the law $\mu$ of the outside option, with Proposition A.1's utilities $u^F=u^P=H+h-\gamma$ and $u^N=\frac{H+L+h+l}2-\gamma$; the finite mean of $\varphi$ (a standing assumption) makes it a genuine expectation.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), pp. 15–16, Proposition 4.1

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

namespace PermBlockchain.Failure

open MeasureTheory

/-- **Proposition 4.1** (p. 15–16): consumer welfare satisfies `W^F_C ≥ W^P_C > W^N_C`. -/
theorem proposition_4_1 {m : ℕ} (M : Model m) (hM : M.Standing) (Δ : ℝ) (hΔ : 0 < Δ)
    (hA : M.Assumption1 Δ) :
    M.WC .P Δ ≤ M.WC .F Δ ∧ M.WC .N Δ < M.WC .P Δ := by sorry

end PermBlockchain.Failure
