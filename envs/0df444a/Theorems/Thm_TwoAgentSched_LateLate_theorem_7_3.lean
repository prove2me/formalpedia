-- Prove2me | Theorems.Thm_TwoAgentSched_LateLate_theorem_7_3
-- name    : TwoAgentSched.LateLate.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:40.997193+00:00
-- url     : https://prove2.me/theorems/dd468025-480a-4e77-8603-380792ed859d
-- title:
--   Theorem 7.3 — $h^* = \min\{h : C(n_A+n_B, h, Q) < +\infty\}$ is the optimal value of $1\|\sum U^A_i : \sum U^B_i \le Q$
-- statement:
--   Two agents $A$ and $B$ share one machine; their $n = n_A + n_B$ jobs $J_1,\dots,J_n$, with processing times $p_j$ and due dates $d_j$, are numbered in EDD order, $d_1 \le \dots \le d_n$. In the problem $1\|\sum U^A_i : \sum U^B_i \le Q$, a sequence of all jobs is feasible if at most $Q$ jobs of $B$ are late, and the objective is the number $\sum U^A_i$ of late jobs of $A$. Let $C(i,h,k)$ be the dynamic-programming table of §7. If the instance is feasible, then $C(n, h, Q) < +\infty$ for some $h$, and
--   $$h^* = \min\{\, h : C(n_A + n_B, h, Q) < +\infty \,\}$$
--   is the optimal value:
--
--   1. some feasible sequence has exactly $h^*$ late $A$-jobs, and
--   2. every feasible sequence has at least $h^*$ late $A$-jobs.
--
--   The theorem turns the table into an exact algorithm for the problem in which agent $B$ tolerates at most $Q$ late jobs and agent $A$ minimizes its own number of late jobs.
--
--   **Formalization Note** Only the correctness half is stated; the running time $O(n_A^2 n_B + n_A n_B^2)$ is not formalized. Feasibility of the instance is a hypothesis (otherwise $h^*$ is the minimum of an empty set). $h^*$ is `Nat.find` of the existence clause. The EDD numbering is the hypothesis that $d$ is monotone, ties allowed. The table uses the corrected boundary $C(0,h,k) = 0$ for all $h,k \ge 0$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 236, Theorem 7.3

import Mathlib
import Definitions.Def_TwoAgentSched_LateLate_Model
import Definitions.Def_TwoAgentSched_LateLate_DPTable

namespace TwoAgentSched.LateLate

/-- Theorem 7.3 (p. 236), correctness half. Jobs are numbered in EDD order (`Monotone d`) and
the instance of `1‖ΣU^A_i : ΣU^B_i ≤ Q` is feasible. Then some `h` has `C(n, h, Q) < +∞`, and
`h* = min{h : C(n, h, Q) < +∞}` is the optimal value: some feasible sequence has exactly `h*`
late `A`-jobs, and every feasible sequence has at least `h*` late `A`-jobs. -/
theorem theorem_7_3 {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) (Q : ℕ) (hd : Monotone d)
    (hfeas : ∃ l : List (Fin n), IsFeasible p d ag Q l) :
    ∃ hex : ∃ h : ℕ, C p d ag n h Q < ⊤,
      (∃ l : List (Fin n), IsFeasible p d ag Q l ∧ numLate p d ag .A l = Nat.find hex) ∧
      ∀ l : List (Fin n), IsFeasible p d ag Q l → Nat.find hex ≤ numLate p d ag .A l := by sorry

end TwoAgentSched.LateLate
