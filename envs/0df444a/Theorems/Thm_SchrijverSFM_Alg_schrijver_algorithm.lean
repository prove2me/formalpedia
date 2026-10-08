-- Prove2me | Theorems.Thm_SchrijverSFM_Alg_schrijver_algorithm
-- name    : SchrijverSFM.Alg.schrijver_algorithm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:42.278979+00:00
-- url     : https://prove2.me/theorems/20f6593f-2a7c-4ae3-b21d-83fa49dd416b
-- title:
--   §4–§5, pp. 351–352 — Schrijver's algorithm: Case 1 returns a minimizer (16), every Case 2 state has a successor, and every run has at most |V|⁶ iterations
-- statement:
--   Let $V = \{0, \dots, n-1\}$ and let $f$ be a submodular real function on the subsets of $V$ with $f(\emptyset) = 0$. Consider Schrijver's algorithm, whose states are convex combinations $x = \lambda_1 h^{\prec_1} + \dots + \lambda_k h^{\prec_k}$ of greedy vectors, with digraph $D$, $P = \{x > 0\}$ and $N = \{x < 0\}$. Then:
--   1. **(Correctness, (16).)** For every valid state in Case 1 (no directed path from $P$ to $N$), the set $U$ of vertices that can reach $N$ minimizes $f$: $f(U) \le f(W)$ for all $W \subseteq V$.
--   2. **(Well-definedness.)** For every valid state in Case 2, one iteration of the algorithm can be carried out.
--   3. **(Running time, §5.)** Every run $S_0 \to S_1 \to \dots \to S_m$ of $m$ iterations from an initial state $S_0 = ((\prec, 1))$ satisfies
--   $$m \le |V|^6.$$
--
--   Together: from any initial order, the algorithm reaches Case 1 after at most $|V|^6$ iterations, and then returns a minimizer of $f$. This is the main result of the paper; it gives a combinatorial algorithm for submodular function minimization whose number of iterations is bounded by a polynomial in $|V|$ alone.
--
--   **Formalization Note** The ground set is `Fin n` and $|V| = n$; "largest" in the choice of $t$ and $s$ refers to the order of `Fin n`; values are real rather than in an arbitrary ordered field. An iteration is the relation `Step` of the setting file, which admits every choice the paper leaves open. Conjunct 2 rules out a vacuous reading of conjunct 3. "Strongly polynomial time" and the number of oracle calls are not formalized (there is no machine model); only the iteration count is.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 351 (§4 Case 1, display (16)), pp. 351–352 (§4 Case 2) and p. 352 (§5, first sentence)

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem schrijver_algorithm {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) :
    (∀ S : State n, Valid S → caseOne f S → ∀ W : Finset (Fin n), f (caseOneSet f S) ≤ f W) ∧
    (∀ S : State n, Valid S → ¬ caseOne f S → ∃ S' : State n, Step f S S') ∧
    (∀ (S : ℕ → State n) (m : ℕ), IsRun f S m → m ≤ n ^ 6) := by sorry
end SchrijverSFM.Alg
