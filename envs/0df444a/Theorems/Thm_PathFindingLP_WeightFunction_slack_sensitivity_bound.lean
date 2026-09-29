-- Prove2me | Theorems.Thm_PathFindingLP_WeightFunction_slack_sensitivity_bound
-- name    : PathFindingLP.WeightFunction.slack_sensitivity_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:48:05.464982+00:00
-- url     : https://prove2.me/theorems/ee3107e7-3fec-4e0e-9643-bd9f853230b7
-- title:
--   Theorem 1, Slack Sensitivity: $\gamma(s,g(s))\le 2$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank $n$ with $1\le n<m$, let $\alpha=1-\left(\log_2\frac{2m}{\mathrm{rank}(A)}\right)^{-1}$ and $\beta=\frac{\mathrm{rank}(A)}{2m}$, and let $s\in\mathbb R^m_{>0}$. If $w\in\mathbb R^m_{>0}$ minimizes the objective $\hat f(s,\cdot)$ of (6) over $\mathbb R^m_{>0}$, then its slack sensitivity (Definition 2) satisfies
--
--   $$
--   \gamma(s,w)=\max_{i\in[m]}\left\|W^{-1/2}\mathbb 1_i\right\|_{P_{S^{-1}A}(w)}\le 2.
--   $$
--
--   Applied to $w=g(s)$ this is the Slack Sensitivity bullet of Theorem 1, $c_\gamma(g)=2$: the Hessian of the weighted barrier at weights $g(s)$ is insensitive to small relative changes of the slacks, uniformly in $m$.
--
--   **Formalization Note** The statement is made for every minimizer. $c_\gamma=2\ge1$, the other half of Definition 4's Slack Sensitivity clause, is immediate. Full column rank of $A$ keeps the inverse in $P_{S^{-1}A}(w)$ from being Mathlib's junk value $0$.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433 (DOI 10.1109/FOCS.2014.52), p. 429, §V.A, Theorem 1 (Properties of Weight Function), Slack Sensitivity bullet; γ from p. 428, §IV.B, Definition 2

import Mathlib
import Definitions.Def_PathFindingLP_WeightFunction_RegularizedObjective
import Definitions.Def_PathFindingLP_WeightFunction_SlackSensitivity

namespace PathFindingLP.WeightFunction
theorem slack_sensitivity_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (w : Fin m → ℝ) (hw : IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s w) :
    slackSensitivity A s w ≤ 2 := by sorry
end PathFindingLP.WeightFunction
