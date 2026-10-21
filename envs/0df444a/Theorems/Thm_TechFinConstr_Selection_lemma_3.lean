-- Prove2me | Theorems.Thm_TechFinConstr_Selection_lemma_3
-- name    : TechFinConstr.Selection.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:09.994164+00:00
-- url     : https://prove2.me/theorems/6aed384a-985e-4f63-bc3f-79d96024c077
-- title:
--   Lemma 3, p. 13 — Φⱼ(p) > 0 for 1 ≤ j ≤ ῑ(p) and Φⱼ(p) = 0 for j > ῑ(p)
-- statement:
--   In Starmans' model, let $p\in\mathscr P$, let $\bar\iota(p)$ be the highest state with $p_i>q_i$ (Lemma 2), and let $\Phi_j(p)=\sum_{i=j}^n(p_i-q_i)/\sum_{i=j}^n q_i$ be the cumulative likelihood ratio. Then
--   $$\Phi_j(p)>0\ \ \text{for all } j\in\{1,\dots,\bar\iota(p)\},\qquad \Phi_j(p)=0\ \ \text{for all } j\in\{\bar\iota(p)+1,\dots,n\}.$$
--
--   Since $\Phi_j(p)$ measures how informative tranche $\bar s^j$ is about effort, the lemma says that exactly the tranches $\bar s^1,\dots,\bar s^{\bar\iota(p)}$, which pay off in the region the entrepreneur improves, are informative.
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), p. 13, Lemma 3 (proof pp. 40–41, Appendix A.6)

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace TechFinConstr.Selection

theorem lemma_3 {n : ℕ} (E : Economy n) (hE : E.Standing) (p : Fin (n + 1) → ℝ) (hp : InP E p) :
    (∀ j : Fin (n + 1), 1 ≤ j.val → j ≤ iotaBar E p → 0 < Phi E p j) ∧
    (∀ j : Fin (n + 1), iotaBar E p < j → Phi E p j = 0) := by sorry

end TechFinConstr.Selection
