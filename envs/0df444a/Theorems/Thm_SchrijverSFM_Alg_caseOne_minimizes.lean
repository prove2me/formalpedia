-- Prove2me | Theorems.Thm_SchrijverSFM_Alg_caseOne_minimizes
-- name    : SchrijverSFM.Alg.caseOne_minimizes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:35.160465+00:00
-- url     : https://prove2.me/theorems/ebc7ed7c-f6c9-4b58-bf63-510c25731dee
-- title:
--   Display (16), §4, Case 1, p. 351 — if D has no path from P to N, the set U of vertices that can reach N minimizes f
-- statement:
--   Let $f$ be a submodular real function on the subsets of $V = \{0, \dots, n-1\}$ with $f(\emptyset) = 0$. Let $x = \lambda_1 h^{\prec_1} + \dots + \lambda_k h^{\prec_k}$ be a state of the algorithm ($k \ge 1$, $\lambda_i > 0$, $\sum_i \lambda_i = 1$), let $D = (V, A)$ with $A = \{(u, v) \mid u \prec_i v \text{ for some } i\}$, $P = \{v \mid x(v) > 0\}$ and $N = \{v \mid x(v) < 0\}$. Suppose $D$ has no directed path from $P$ to $N$ (Case 1), and let $U$ be the set of vertices of $D$ that can reach $N$ by a directed path (of length $\ge 0$). Then
--   $$f(U) \le f(W) \qquad \text{for all } W \subseteq V.$$
--
--   This is the termination condition of the algorithm: when it stops, $U$ is a minimizer of $f$.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 351, §4 Case 1, display (16)

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem caseOne_minimizes {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) (S : State n) (hS : Valid S) (h1 : caseOne f S) :
    ∀ W : Finset (Fin n), f (caseOneSet f S) ≤ f W := by sorry
end SchrijverSFM.Alg
