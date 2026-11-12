-- Prove2me | Theorems.Thm_SepQPTardos_Main_eq_19_descent_bound
-- name    : SepQPTardos.Main.eq_19_descent_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:35.241587+00:00
-- url     : https://prove2.me/theorems/7e7e6fd0-5d30-491d-b265-1a6e6628295e
-- title:
--   §4.2, eq. (19) — the descent LP (18) has a finite optimum $0\le V_F\le\|(z-t)_N\|_1$
-- statement:
--   In the context of §4, let $t$ be a trial point (a solution of (17) built from an optimal solution of (15)) and $g=Qt+c$. Then the descent LP (18),
--
--   $$V_F=\max\ -g^\top d\quad\text{subject to}\quad Ad=0,\ \ d_{\bar F}\ge0,\ \ -1/q_e\le d_e\le1/q_e\ (e\in N),$$
--
--   has a bounded set of objective values and attains its optimum, and
--
--   $$0\le V_F\le\|(z-t)_N\|_1\qquad\text{for every optimum } z \text{ on } P_F(b).\tag{19}$$
--
--   $V_F$ measures first-order descent from $t$ along recession directions of $P_F(b)$; it is one half of the scale $E_F$.
--
--   Differences from the source:
--   - generalization: A ∈ ℤ^{r×m}, rational b, c, q → integer A, real b, c, q; reason: the argument uses no rationality of b, c, q; rational data are a special case
--   - generalization: §4 runs under (7): feasible and finite, 1 ≤ r < m, N ≠ ∅, and after deleting redundant rows of A → none of these assumed; only q ≥ 0, an optimal pair (x*, π*) satisfying (8), and F ⊆ T*; reason: the argument does not use them; an instance satisfying (7) is a special case
--   - generalization: a basic optimal solution of (15) and the solution of (17) returned by rational elimination → every optimal solution (u, α_F) of (15) and every solution t of (17) built from it; reason: the argument uses only optimality in (15) and the equations (17); the paper's choice is one instance
--   - encoding: V_F, the optimal value of (18) → the supremum of the feasible objective values, with boundedness and attainment asserted; reason: the supremum is the LP optimum once it is attained, which the statement asserts
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §4.2, LP (18) and eq. (19), pp. 8–9

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Circuits
import Definitions.Def_SepQPTardos_Main_Analysis

open Matrix

namespace SepQPTardos.Main

/-- §4.2, eq. (19) (Cui–Li–Miao, STOC 2027 #829, pp. 8–9). In the context of §4, let `t` be a
trial point (a solution of (17) whose `v` comes from an optimal solution of (15)) and
`g = Qt + c`. The descent LP (18) attains a finite optimum `V_F`, and
`0 ≤ V_F ≤ ‖(z − t)_N‖₁` for every optimum `z` on `P_F(b)`. -/
theorem eq_19_descent_bound {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ)
    (q c : Fin m → ℝ) (xs : Fin m → ℝ) (πs : Fin r → ℝ) (F : Finset (Fin m))
    (hctx : Sec4Context A b q c xs πs F) (t : Fin m → ℝ) (ht : IsTrialPoint A b q c F t) :
    BddAbove {v | ∃ d, LP18Feas A q F d ∧ v = -(grad q c t ⬝ᵥ d)} ∧
    (∃ d, LP18Feas A q F d ∧ -(grad q c t ⬝ᵥ d) = VF A q c F t) ∧
    0 ≤ VF A q c F t ∧
    ∀ z, IsMinimizer (PF A b F) (Phi q c) z →
      VF A q c F t ≤ ∑ e ∈ Nset q, |z e - t e| := by sorry

end SepQPTardos.Main
