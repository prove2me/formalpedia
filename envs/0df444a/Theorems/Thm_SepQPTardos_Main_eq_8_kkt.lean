-- Prove2me | Theorems.Thm_SepQPTardos_Main_eq_8_kkt
-- name    : SepQPTardos.Main.eq_8_kkt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:06.582224+00:00
-- url     : https://prove2.me/theorems/b888c00d-359b-45cb-bba3-2875d56f72f0
-- title:
--   §2.2, eq. (8) — the KKT conditions are necessary and sufficient for optimality
-- statement:
--   Let $A\in\mathbb R^{r\times m}$, $b\in\mathbb R^r$, $c\in\mathbb R^m$ and $q\ge0$, $Q=\operatorname{diag}(q)$. A feasible point $x$ of (1) is optimal if and only if there is $\pi\in\mathbb R^r$ with
--
--   $$Ax=b,\quad x\ge0,\quad \sigma=Qx+c-A^\top\pi\ge0,\quad x^\top\sigma=0.\tag{8}$$
--
--   Because the constraints are linear, no constraint qualification is needed. The conditions certify optimality of the algorithm's output and justify the nonnegativity relaxations of §4.
--
--   Differences from the source:
--   - generalization: A ∈ ℤ^{r×m}, rational b, c, q → real A, b, c, q; reason: the normal-cone argument uses no integrality; the paper's instances are a special case
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §2.2, eq. (8), p. 5

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem

namespace SepQPTardos.Main

/-- §2.2, eq. (8) (Cui–Li–Miao, STOC 2027 #829, p. 5): for `q ≥ 0`, a feasible point `x` of (1)
is optimal if and only if some `π` satisfies the KKT system (8):
`σ = Qx + c − Aᵀπ ≥ 0` and `xᵀσ = 0`. -/
theorem eq_8_kkt {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℝ) (b : Fin r → ℝ) (q c : Fin m → ℝ)
    (hq : ∀ e, 0 ≤ q e) (x : Fin m → ℝ) (hx : Feasible A b x) :
    IsOptimal A b q c x ↔ ∃ π : Fin r → ℝ, KKT A b q c x π := by sorry

end SepQPTardos.Main
