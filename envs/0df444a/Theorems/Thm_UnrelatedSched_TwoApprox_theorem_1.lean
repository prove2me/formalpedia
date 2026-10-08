-- Prove2me | Theorems.Thm_UnrelatedSched_TwoApprox_theorem_1
-- name    : UnrelatedSched.TwoApprox.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:17:09.649098+00:00
-- url     : https://prove2.me/theorems/960e4165-8673-4778-944c-096b35d74c95
-- title:
--   Theorem 1 (Rounding Theorem) — every vertex of (LP) rounds to a 0-1 solution of (IP) on its support
-- statement:
--   Let $P=(p_{ij})\in\mathbb N^{m\times n}$, deadlines $d_1,\dots,d_m\in\mathbb R$ and a threshold $t\ge 0$. Suppose the linear program
--   $$\sum_{i\in M_j(t)}x_{ij}=1\ (j=1,\dots,n),\qquad\sum_{j\in J_i(t)}p_{ij}x_{ij}\le d_i\ (i=1,\dots,m),\qquad x_{ij}\ge 0\ (j\in J_i(t))\qquad\text{(LP)}$$
--   is feasible, and let $\tilde x$ be any vertex of this polytope. Then $\tilde x$ can be rounded to a feasible solution $\bar x$ of the integer program
--   $$\sum_{i\in M_j(t)}x_{ij}=1,\qquad\sum_{j\in J_i(t)}p_{ij}x_{ij}\le d_i+t,\qquad x_{ij}\in\{0,1\}\qquad\text{(IP)}$$
--   with $\bar x_{ij}=1$ only where $\tilde x_{ij}>0$. In schedule form: there is a schedule $\sigma$ with $\tilde x_{\sigma(j)j}>0$ for every job, $p_{\sigma(j)j}\le t$, and load at most $d_i+t$ on every machine $i$.
--
--   The Rounding Theorem is the key tool of the paper: it converts a fractional solution of the deadline LP into a schedule that overshoots each deadline by at most $t$, the largest processing time allowed.
--
--   **Formalization Note** The paper states "and this rounding can be done in polynomial time"; running time is not formalized. "Rounding" is formalized as support containment ($\bar x_{ij}=1\Rightarrow\tilde x_{ij}>0$), which in particular keeps every integral entry $\tilde x_{ij}=1$. The paper takes $d\in\mathbb Z_+^m$ and $t\in\mathbb Z_+$; the proof never uses integrality, so real $d$ and real $t\ge 0$ are allowed. Feasibility of (LP) is implied by the existence of a vertex.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 3, Theorem 1

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

/-- Theorem 1 (Rounding Theorem), p. 3: every vertex `x̃` of (LP) can be rounded to a 0-1 solution of
(IP) supported on `x̃`. -/
theorem theorem_1 {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (x : Matrix (Fin m) (Fin n) ℝ) (hx : IsLPVertex P d t x) :
    ∃ σ : Fin n → Fin m, SupportedOn x σ ∧ IPFeasible P d t σ := by sorry

end UnrelatedSched.TwoApprox
