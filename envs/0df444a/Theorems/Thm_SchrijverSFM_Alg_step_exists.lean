-- Prove2me | Theorems.Thm_SchrijverSFM_Alg_step_exists
-- name    : SchrijverSFM.Alg.step_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:29.075993+00:00
-- url     : https://prove2.me/theorems/cbd53912-e8d6-4be6-83f6-e467b1a4fa9b
-- title:
--   §4, pp. 351–352 — in Case 2 an iteration of the algorithm can always be carried out
-- statement:
--   Let $f$ be a submodular real function on the subsets of $V = \{0, \dots, n-1\}$ with $f(\emptyset) = 0$, and let $S = ((\prec_1, \lambda_1), \dots, (\prec_k, \lambda_k))$ be a valid state ($k \ge 1$, $\lambda_i > 0$, $\sum_i \lambda_i = 1$) in Case 2: the digraph $D$ has a directed path from $P = \{x > 0\}$ to $N = \{x < 0\}$. Then there is a state $S'$ obtained from $S$ by one iteration of the algorithm:
--   $$\exists\, S' : \ S \to S' \text{ is an iteration.}$$
--   Here an iteration (defined in the setting file) chooses $t$ and $s$ by the rule of §4, an index of an order with $|(s,t]_{\prec_1}| = \alpha$, an output $\delta$ of the subroutine (17), the point $x'$ of the segment $\overline{xy}$ closest to $y = x + \lambda_1\delta(\chi^t - \chi^s)$ with $x'(t) \le 0$, and a decomposition of $x'$ with at most $|V|$ terms using only the orders $\prec_j$ ($j \ne 1$), $\prec_1^{s,u}$ ($u \in (s,t]_{\prec_1}$), and $\prec_1$ only if $x'(t) = 0$.
--
--   This says the description of the algorithm in §4 is well defined: every choice the paper makes is possible, and the Carathéodory reduction yields at most $|V|$ terms.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), pp. 351–352, §4 Case 2, displays (17)–(18) and the two paragraphs of p. 352

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem step_exists {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) (S : State n) (hS : Valid S) (h2 : ¬ caseOne f S) :
    ∃ S' : State n, Step f S S' := by sorry
end SchrijverSFM.Alg
