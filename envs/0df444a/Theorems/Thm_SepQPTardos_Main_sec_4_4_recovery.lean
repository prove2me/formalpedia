-- Prove2me | Theorems.Thm_SepQPTardos_Main_sec_4_4_recovery
-- name    : SepQPTardos.Main.sec_4_4_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:41.355694+00:00
-- url     : https://prove2.me/theorems/63ae9173-0b99-47a0-a946-1d006bfbd81b
-- title:
--   §4.4 — recovery by linear programming when $E_F=0$
-- statement:
--   In the context of §4, let $t$ be a trial point with $E_F=0$. Then:
--
--   1. $\alpha_F=V_F=0$ and $t_{\bar F}=0$;
--   2. $t$ is an optimum on $P_F(b)$, and $t_N=x^*_N\ge0$;
--   3. LP (25), $\min\{c_Z^\top x_Z: A_Zx_Z=b-A_Nt_N,\ x_Z\ge0\}$ (written for the combined vector $x$ with $x_N=t_N$), is feasible and has an optimum, and every optimum, combined with $x_N=t_N$, is an optimum of (1); if $Z=\emptyset$, then $t$ itself is an optimum of (1);
--   4. for every optimum $x$ of (1) the system (26),
--   $$A^\top\pi\le Qx+c,\qquad (A^\top\pi)_e=(Qx+c)_e\ \text{ for every } e \text{ with } x_e>0,$$
--   is feasible, and each of its solutions $\pi$ makes $(x,\pi)$ satisfy (8).
--
--   These two LPs end the algorithm with an exact optimal primal–dual pair.
--
--   Differences from the source:
--   - generalization: A ∈ ℤ^{r×m}, rational b, c, q → integer A, real b, c, q; reason: the argument uses no rationality of b, c, q; rational data are a special case
--   - generalization: §4 runs under (7): feasible and finite, 1 ≤ r < m, N ≠ ∅, and after deleting redundant rows of A → none of these assumed; only q ≥ 0, an optimal pair (x*, π*) satisfying (8), and F ⊆ T*; reason: the argument does not use them; an instance satisfying (7) is a special case
--   - generalization: a basic optimal solution of (15) and the solution of (17) returned by rational elimination → every optimal solution (u, α_F) of (15) and every solution t of (17) built from it; reason: the argument uses only optimality in (15) and the equations (17); the paper's choice is one instance
--   - generalization: (26) for the optimum x obtained from (25) → (26) for every optimum x of (1); reason: the source's argument uses only that x is an optimum; the optimum from (25) is one such x
--   - reading: this LP is feasible and finite → LP (25) is feasible and has an optimum; reason: a finite LP attains its optimum
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §4.4, recovery by linear programming, LPs (25) and (26), p. 10

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Circuits
import Definitions.Def_SepQPTardos_Main_Analysis

open Matrix

namespace SepQPTardos.Main

/-- §4.4, recovery by linear programming (Cui–Li–Miao, STOC 2027 #829, p. 10). In the context
of §4, let `t` be a trial point with `E_F = 0`. Then `α_F = V_F = 0` and `t_{F̄} = 0`; `t` is an
optimum on `P_F(b)` and `t_N = x*_N ≥ 0`; LP (25) (`x_N = t_N`, `x_Z ≥ 0`, `Ax = b`,
minimise `c_Zᵀx_Z`) is feasible and has an optimum, and each of its optima is an optimum of
(1); if `Z = ∅`, `t` itself is an optimum of (1); and for every optimum `x` of (1) system (26)
is feasible and each of its solutions `π` makes `(x, π)` satisfy (8). -/
theorem sec_4_4_recovery {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ)
    (q c : Fin m → ℝ) (xs : Fin m → ℝ) (πs : Fin r → ℝ) (F : Finset (Fin m))
    (hctx : Sec4Context A b q c xs πs F) (t : Fin m → ℝ) (ht : IsTrialPoint A b q c F t)
    (hE : EF A b q c F t = 0) :
    alphaF A b F = 0 ∧ VF A q c F t = 0 ∧ (∀ e, e ∉ F → t e = 0) ∧
    IsMinimizer (PF A b F) (Phi q c) t ∧ (∀ e ∈ Nset q, t e = xs e ∧ 0 ≤ t e) ∧
    (∃ x, LP25Feas A b q t x ∧ ∀ y, LP25Feas A b q t y → LP25Obj q c x ≤ LP25Obj q c y) ∧
    (∀ x, (LP25Feas A b q t x ∧ ∀ y, LP25Feas A b q t y → LP25Obj q c x ≤ LP25Obj q c y) →
      IsOptimal (castMat A) b q c x) ∧
    (Zset q = ∅ → IsOptimal (castMat A) b q c t) ∧
    ∀ x, IsOptimal (castMat A) b q c x →
      (∃ π : Fin r → ℝ, Sys26 A q c x π) ∧
      ∀ π : Fin r → ℝ, Sys26 A q c x π → KKT (castMat A) b q c x π := by sorry

end SepQPTardos.Main
