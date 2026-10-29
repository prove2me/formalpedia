-- Prove2me | Theorems.Thm_PochetWolsey_Decomposition_formulation_bounds
-- name    : PochetWolsey.Decomposition.formulation_bounds
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:45.124274+00:00
-- url     : https://prove2.me/theorems/79beb432-8caa-4814-aacc-39116d6ab2e4
-- title:
--   Proposition 6.4 — equivalent formulation bounds (printed convention)
-- statement:
--   Let $P_Y=\{x\ge0:Ax\ge b\}$ have rational data, let $Y=P_Y\cap\mathbb Z^n$, and let $P_Z=\{x\ge0:Dx\ge d\}$. All dimensions are finite; $c$ and the linking data are real. Let $R=\{x\ge0:Bx\ge e\}$ and $E=\{x\ge0:\exists v\in\mathbb R^p, Fx+Gv\ge g\}$ be tight descriptions: $R=E=\operatorname{conv}(Y)$. For a finite family of cuts $a_i x\ge r_i$ valid on $Y$, put $C=P_Y\cap P_Z\cap\{x:a_i x\ge r_i\}$.
--
--   An exact separator returns no cut precisely at points of $\operatorname{conv}(Y)$; every returned cut is valid for $Y$ and strictly violated by the query point. Assume the cutting-plane run has terminated at a minimizer $\bar x$ over $C$ where that separator returns no cut. Write $S_1=R\cap P_Z$, $S_2=E\cap P_Z$, and $S_3=C$. With the preceding paragraph's literal convention $z_i=\sup_{x\in S_i}cx$, the printed assertion is
--   $$
--   z_1=z_2=z_3=\min_{x\in\operatorname{conv}(Y)\cap P_Z}cx.
--   $$
--   All three suprema and the minimum are asserted to be attained. This records the source's comparison of direct formulations, projections, and completed cutting-plane relaxations.
--
--   **Formalization Note** This faithful item is false: the page defines each $z_i$ by maximization but equates it to a minimum. Finding F1 gives $Y=\{0,1\}$, all three sets $[0,1]$, and $c=1$. Values use extended reals to avoid default real infima; the finite minimum is explicitly witnessed. Exact separation is encoded by its oracle specification and terminal-state conditions, without assuming that the finite cut region equals the hull.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 198 (PDF 212), Proposition 6.4; Section 6.3.1, pp. 197–198

import Mathlib

namespace PochetWolsey.Decomposition

theorem formulation_bounds {n m q t p a s : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (D : Matrix (Fin q) (Fin n) ℝ) (d : Fin q → ℝ)
    (c : Fin n → ℝ)
    (B : Matrix (Fin t) (Fin n) ℝ) (e : Fin t → ℝ)
    (F : Matrix (Fin a) (Fin n) ℝ) (G : Matrix (Fin a) (Fin p) ℝ)
    (g : Fin a → ℝ)
    (cuts : Matrix (Fin s) (Fin n) ℝ) (rhs : Fin s → ℝ)
    (sep : (Fin n → ℝ) → Option ((Fin n → ℝ) × ℝ)) :
    let PY : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      ∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j}
    let Y : Set (Fin n → ℝ) := {x | x ∈ PY ∧ ∀ j, ∃ z : ℤ, x j = (z : ℝ)}
    let PZ : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      ∀ i, d i ≤ ∑ j, D i j * x j}
    let direct : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      ∀ i, e i ≤ ∑ j, B i j * x j}
    -- The auxiliary sum over Fin p remains even when the original dimension n is zero.
    let Q : Set ((Fin n → ℝ) × (Fin p → ℝ)) := {xv |
      (∀ j, 0 ≤ xv.1 j) ∧
      ∀ i, g i ≤ (∑ j, F i j * xv.1 j) + ∑ j, G i j * xv.2 j}
    let projection : Set (Fin n → ℝ) := {x | ∃ v : Fin p → ℝ, (x, v) ∈ Q}
    let cutting : Set (Fin n → ℝ) := {x | x ∈ PY ∩ PZ ∧
      ∀ i, rhs i ≤ ∑ j, cuts i j * x j}
    let cost : (Fin n → ℝ) → ℝ := fun x => ∑ j, c j * x j
    let value : Set (Fin n → ℝ) → EReal := fun S =>
      sSup ((fun x => (cost x : EReal)) '' S)
    direct = convexHull ℝ Y → projection = convexHull ℝ Y →
    (∀ i, ∀ y ∈ Y, rhs i ≤ ∑ j, cuts i j * y j) →
    (∀ x, sep x = none ↔ x ∈ convexHull ℝ Y) →
    (∀ x α β, sep x = some (α, β) →
      (∀ y ∈ Y, β ≤ ∑ j, α j * y j) ∧ (∑ j, α j * x j) < β) →
    (∃ xbar ∈ cutting, (∀ x ∈ cutting, cost xbar ≤ cost x) ∧ sep xbar = none) →
    value (direct ∩ PZ) = value (projection ∩ PZ) ∧
    value (projection ∩ PZ) = value cutting ∧
    value cutting = sInf ((fun x => (cost x : EReal)) '' (convexHull ℝ Y ∩ PZ)) ∧
    (∀ S ∈ [direct ∩ PZ, projection ∩ PZ, cutting],
      ∃ xmax ∈ S, (∀ x ∈ S, cost x ≤ cost xmax) ∧ value S = (cost xmax : EReal)) ∧
    ∃ xstar ∈ convexHull ℝ Y ∩ PZ,
      (∀ x ∈ convexHull ℝ Y ∩ PZ, cost xstar ≤ cost x) ∧
      sInf ((fun x => (cost x : EReal)) '' (convexHull ℝ Y ∩ PZ)) =
        (cost xstar : EReal) := by sorry

end PochetWolsey.Decomposition
