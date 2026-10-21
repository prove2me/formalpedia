-- Prove2me | Theorems.Thm_PolyClinch_TwoSided_theorem_3_9
-- name    : PolyClinch.TwoSided.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:08.020629+00:00
-- url     : https://prove2.me/theorems/c5629eff-67ec-4eb0-b13f-3521892e61f4
-- title:
--   Theorem 3.9, p. 13 — at termination, (y, π) of Algorithm 1 equals ((w(E_i))_i, p) of Algorithm 2
-- statement:
--   Let $\mathcal I$ be valid public information and use the same $\varepsilon>0$ in both algorithms. Let $(w,p,\dots)$ be the terminal state of any run of Algorithm 2 on the extended market, and $(y,\pi,\dots)$ the terminal state of any run of Algorithm 1 on the reduced one-sided market. Then, for every buyer $i$ of the extended market (real and virtual),
--   $$
--   y_i=w(E_i),\qquad \pi_i=p_i .
--   $$
--   So the buyers' outcomes in Mechanism 2 coincide with those of the polyhedral clinching auction on the reduced one-sided market, whatever maximal clinching vectors Algorithm 2 picks.
--
--   **Formalization Note** Both outputs are quantified universally over runs; Algorithm 2's clinching vector is not unique (§4), and the theorem asserts the equality for every choice.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, p. 13, Theorem 3.9; proof in §5.2, pp. 25–28

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Clinching

namespace PolyClinch.TwoSided

/-- Theorem 3.9 (Hirai–Sato p. 13). With the same `ε` in both algorithms, at termination the
output `(y, π)` of Algorithm 1 on the reduced one-sided market equals `((w(E_i))_{i}, p)` of
Algorithm 2 on the preprocessed market, for every run of each. -/
theorem theorem_3_9 {n m : ℕ} (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε)
    (I : PublicInfo E) (hI : Valid E ε I)
    (S : Alg2State E) (hS : Alg2Outcome E I ε S)
    (S₁ : Alg1State (n + m)) (hS₁ : Alg1Outcome (reducedP E I) (extBudget E I) (extBid E I) ε S₁) :
    S₁.y = (fun i => ∑ e ∈ extEdgesOfBuyer E i, S.w e) ∧ S₁.pay = S.p := by sorry

end PolyClinch.TwoSided
