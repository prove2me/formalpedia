-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_theorem_1
-- name    : StengelZeroSum.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:26:51.956312+00:00
-- url     : https://prove2.me/theorems/deb9bbc7-d0a1-5fb5-ad8c-991b1b7b5a3f
-- title:
--   Theorem 1 (LP duality) — if (1) and (2) are feasible, some feasible $x,y$ have $c^\top x=y^\top b$ and are optimal
-- statement:
--   Let $A$ be a real $m\times n$ matrix ($m,n\ge1$), $b\in\mathbb R^m$ and $c\in\mathbb R^n$. Consider the primal LP and its dual
--
--   $$
--   \text{(1)}\ \ \max_x\ c^\top x\ \ \text{s.t.}\ Ax\le b,\ x\ge\mathbf 0,
--   \qquad
--   \text{(2)}\ \ \min_y\ y^\top b\ \ \text{s.t.}\ y^\top A\ge c^\top,\ y\ge\mathbf 0 .
--   $$
--
--   If both (1) and (2) are feasible, then there exist a feasible $x$ for (1) and a feasible $y$ for (2) with
--
--   $$
--   c^\top x=y^\top b ,
--   $$
--
--   and these $x$ and $y$ are optimal solutions of (1) and (2) respectively.
--
--   This is the strong LP duality theorem in the form the paper uses: equality of the objective values is attained by a feasible pair as soon as both programs are feasible.
--
--   **Formalization Note** Feasibility and optimality are the published `PrimalFeasible`, `DualFeasible`, `PrimalOptimal`, `DualOptimal` of `VanderbeiLP.StrictComp`, which describe exactly the LP pair (1), (2). $y^\top b$ is written `b ⬝ᵥ y`.
--
--   Differences from the source: none.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 1, p.5 (LPs (1), (2), pp.4–5)

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair

open Matrix VanderbeiLP.StrictComp

namespace StengelZeroSum.Supplement

/-- **Theorem 1 (LP duality)**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 1, p.5:
"If the primal LP (1) and the dual LP (2) are feasible, then there exist feasible `x` and `y`
with `c⊤x = y⊤b`, which are therefore optimal solutions."

The primal LP (1) is `maximize c⊤x subject to Ax ≤ b, x ≥ 0` (p.4), the dual LP (2) is
`minimize y⊤b subject to y⊤A ≥ c⊤, y ≥ 0` (p.5).

**Formalization Note** (1) and (2) are the published `PrimalFeasible`/`DualFeasible`/
`PrimalOptimal`/`DualOptimal` of `VanderbeiLP.StrictComp` (same LP pair). `y⊤b` is
`b ⬝ᵥ y`. `0 < m`, `0 < n` are the paper's standing assumption (p.4). -/
theorem theorem_1 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : ∃ x : Fin n → ℝ, PrimalFeasible A b x) (hD : ∃ y : Fin m → ℝ, DualFeasible A c y) :
    ∃ (x : Fin n → ℝ) (y : Fin m → ℝ), PrimalFeasible A b x ∧ DualFeasible A c y ∧
      c ⬝ᵥ x = b ⬝ᵥ y ∧ PrimalOptimal A b c x ∧ DualOptimal A b c y := by sorry

end StengelZeroSum.Supplement
