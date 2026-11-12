-- Prove2me | Theorems.Thm_SepQPTardos_Main_sec_2_2_attainment
-- name    : SepQPTardos.Main.sec_2_2_attainment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:06.901462+00:00
-- url     : https://prove2.me/theorems/aec66274-a7ee-4dfc-935a-e47d547aadb1
-- title:
--   §2.2 — a feasible separable convex QP is bounded below iff (5) is feasible, and then attains its minimum
-- statement:
--   Let $A\in\mathbb R^{r\times m}$, $b\in\mathbb R^r$, $c\in\mathbb R^m$ and $q\in\mathbb R^m$ with $q\ge0$, and suppose problem (1) is feasible. Write $Z=\{e:q_e=0\}$. Then
--
--   1. $\Phi$ is bounded below on the feasible set $\{x: Ax=b,\ x\ge0\}$ if and only if system (5), $A_Z^\top\pi_0\le c_Z$ with $\pi_0$ free, is feasible;
--   2. if (5) is feasible, $\Phi$ attains its minimum on the feasible set.
--
--   Equivalently, a feasible instance is unbounded below exactly when (5) is infeasible, in which case a Farkas certificate of (5) yields the unboundedness certificate; otherwise an optimum exists. This is the reduction of §2.2 to the feasible, finite case.
--
--   Differences from the source:
--   - generalization: A ∈ ℤ^{r×m}, rational b, c, q → real A, b, c, q; reason: the argument uses no integrality or rationality; the paper's instances are a special case
--   - generalization: N ≠ ∅ (system (5) is tested only in that case) → any q ≥ 0; reason: for N = ∅, (5) is dual feasibility of the LP and the claim is LP duality; instances with N ≠ ∅ are a special case
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §2.2, p. 5 (paragraph ending "if and only if (5) is infeasible")

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem

open Matrix

namespace SepQPTardos.Main

/-- §2.2, boundedness and attainment (Cui–Li–Miao, STOC 2027 #829, p. 5): for a feasible
instance of (1) with `q ≥ 0`, `Φ` is bounded below on the feasible set if and only if system
(5), `A_Zᵀπ₀ ≤ c_Z`, is feasible; and when (5) is feasible, `Φ` attains its minimum on the
feasible set. -/
theorem sec_2_2_attainment {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℝ) (b : Fin r → ℝ)
    (q c : Fin m → ℝ) (hq : ∀ e, 0 ≤ q e) (hfeas : ∃ x, Feasible A b x) :
    (BddBelow (Phi q c '' {x | Feasible A b x}) ↔ ∃ π₀ : Fin r → ℝ, Sys5 A q c π₀) ∧
    ((∃ π₀ : Fin r → ℝ, Sys5 A q c π₀) → ∃ x, IsOptimal A b q c x) := by sorry

end SepQPTardos.Main
