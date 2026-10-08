-- Prove2me | Theorems.Thm_RobustPower_CostGap_robust_value_ge_one
-- name    : RobustPower.CostGap.robust_value_ge_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:22.554607+00:00
-- url     : https://prove2.me/theorems/e50e28ff-e18c-44b3-a2f1-156ec03e280a
-- title:
--   Proof of Theorem 3.1, p. 23 — in the instance of Theorem 3.1, z_Rob(b, d) ≥ 1
-- statement:
--   Consider the instance of Theorem 3.1: no first-stage variables ($n_1=0$, so $c=0$ and $A=0$), $n\ge1$ continuous second-stage variables, a single constraint with $B=[1,1,\dots,1]\in\mathbb R^{1\times n}$ and right-hand side $b(\omega)=1$ in every scenario, and a cost map $d:\Omega\to\mathbb R^n$ whose range is exactly the cube $[0,1]^n$. Then the optimal value of the robust problem $\Pi_{\mathrm{Rob}}(b,d)$ satisfies
--
--   $$
--   z_{\mathrm{Rob}}(b,d)\ \ge\ 1 .
--   $$
--
--   This is the robust half of the gap in Theorem 3.1: the scenario with $d(\omega)=(1,\dots,1)$ is among the scenarios, and the single robust decision must cover it.
--
--   **Formalization Note** $z_{\mathrm{Rob}}$ is the extended-real infimum of (1.5); the statement does not assume that an optimal robust solution exists. No probability measure is involved.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 23, proof of Theorem 3.1, display z_Rob(b, d) ≥ 1

import Mathlib
import Definitions.Def_RobustPower_CostGap_Problems

open MeasureTheory Matrix

namespace RobustPower.CostGap

/-- Proof of Theorem 3.1, p. 23: in the instance of Theorem 3.1, `z_Rob(b, d) ≥ 1`. -/
theorem robust_value_ge_one {n : ℕ} (hn : 0 < n) {Ω : Type*}
    (d : Ω → Fin n → ℝ) (hrange : Set.range d = Set.Icc 0 1) :
    (1 : EReal) ≤
      zRobBD (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
          (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ := by sorry

end RobustPower.CostGap
