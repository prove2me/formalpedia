-- Prove2me | Theorems.Thm_SubstOverbooking_Structure_tp_dtp_strong_duality
-- name    : SubstOverbooking.Structure.tp_dtp_strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:03.687815+00:00
-- url     : https://prove2.me/theorems/a4bee272-3858-4631-9ed8-3e8eee2127d4
-- title:
--   §2.2, p. 86 — TP and DTP are feasible for z ⩾ 0 and their optimal values are equal and finite
-- statement:
--   Let $a_{ij}$ be arbitrary net benefits, $c_j \ge 0$ for the real inventory classes $j = 1, \dots, m$ (class $0$ uncapacitated), and $z \in \mathbb R^n$ with $z \ge 0$. Then:
--
--   1. the transportation problem (TP) attains its optimum: there is a feasible assignment $y$ with $\sum_{i,j} a_{ij} y_{ij} = V_0(z, c)$;
--   2. weak duality: for every dual-feasible $(\mu, \lambda)$,
--   $$V_0(z, c) \le \sum_{i=1}^n z_i \mu_i + \sum_{j=0}^m c_j \lambda_j;$$
--   3. strong duality: some dual-feasible $(\mu, \lambda)$ achieves equality.
--
--   In particular $V_0(z, c)$ is the common finite optimal value of TP and DTP. This is the linear-programming fact on which the structural lemmas about $V_0$ rest.
--
--   **Formalization Note.** Dual feasibility includes $\lambda_0 = 0$, the dual counterpart of the uncapacitated virtual class $0$.
-- source:
--   Karaesmen & van Ryzin, Overbooking with Substitutable Inventory Classes, Operations Research 52(1):83–104 (2004), p. 86, §2.2, after (5)

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting

namespace SubstOverbooking.Structure

theorem tp_dtp_strong_duality {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) (c : Fin (m + 1) → ℝ)
    (hc : ∀ j, j ≠ 0 → 0 ≤ c j) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∃ y, IsTPFeasible c z y ∧ tpObjective a y = V0 a c z) ∧
    (∀ μ lam, IsDTPFeasible a μ lam → V0 a c z ≤ dtpObjective c z μ lam) ∧
    (∃ μ lam, IsDTPFeasible a μ lam ∧ dtpObjective c z μ lam = V0 a c z) := by sorry

end SubstOverbooking.Structure
