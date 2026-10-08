-- Prove2me | Theorems.Thm_RobustPower_SimplexGap_robust_value_ge_one
-- name    : RobustPower.SimplexGap.robust_value_ge_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:28:45.688426+00:00
-- url     : https://prove2.me/theorems/e18f94ff-fe42-445a-9e92-e83137467cc4
-- title:
--   Proof of Theorem 2.6, p. 20 — every robust solution has yⱼ ≥ 1, so z_Rob(b) ≥ 1
-- statement:
--   Consider the instance of Theorem 2.6: $n\ge 3$, no first stage ($n_1=0$, so $A=0$, $c=0$), $n_2=m=n$, $B=I_n$, cost vector $d=e_n=(0,\dots,0,1)$, no integer coordinates, and scenarios $b:\Omega\to\mathbb R^n$ whose uncertainty set $I_b(\Omega)=\{b(\omega)\mid\omega\in\Omega\}$ is the corner simplex $\Delta_n=\{b\ge 0:\sum_j b_j\le 1\}$. Then
--
--   1. every feasible solution $y\ge 0$ of the robust problem $\Pi_{\mathrm{Rob}}(b)$, i.e. with $I_n y\ge b(\omega)$ for all $\omega\in\Omega$, satisfies $y_j\ge 1$ for all $j=1,\dots,n$;
--   2. consequently
--   $$z_{\mathrm{Rob}}(b)\ \ge\ 1.$$
--
--   This is the robust half of the proof of Theorem 2.6: the robust solution must cover every vertex $e_j$ of the simplex simultaneously.
--
--   **Formalization Note** The first-stage variable lives in $\mathbb R^0$; the integer coordinate sets are empty. $z_{\mathrm{Rob}}(b)$ is the `EReal` infimum of the `Problems` file. Only the range of $b$ matters here; no measure is involved.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 20, proof of Theorem 2.6 (display z_Rob(b) ≥ 1)

import Mathlib
import Definitions.Def_RobustPower_SimplexGap_Problems
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

namespace RobustPower.SimplexGap

/-- Proof of Theorem 2.6, p. 20: on the instance of Theorem 2.6, every robust-feasible `y` has
`yⱼ ≥ 1` for all `j`, hence `z_Rob(b) ≥ 1`. -/
theorem robust_value_ge_one (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} (b : Ω → Fin n → ℝ)
    (hb : Set.range b = cornerSimplex n) :
    (∀ (x : Fin 0 → ℝ) (y : Fin n → ℝ),
        RobFeasible (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅ x y →
          ∀ j, 1 ≤ y j) ∧
      (1 : EReal) ≤ zRob (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ)
        (0 : Fin 0 → ℝ) (lastUnit n) b ∅ ∅ := by sorry

end RobustPower.SimplexGap
