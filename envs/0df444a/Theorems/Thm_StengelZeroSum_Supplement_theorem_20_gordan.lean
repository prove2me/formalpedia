-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_theorem_20_gordan
-- name    : StengelZeroSum.Supplement.theorem_20_gordan
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:27:38.095283+00:00
-- url     : https://prove2.me/theorems/583d7f7c-0a47-5dca-84e4-1f3129ec770f
-- title:
--   Gordan's Theorem (20) — $Ax=0$ has no $x\ge0$, $x\ne0$ iff some $y$ has $y^\top A>0^\top$
-- statement:
--   Let $A$ be a real $m\times n$ matrix ($m,n\ge1$). Then
--
--   $$
--   \nexists\,x\in\mathbb R^n:\ Ax=\mathbf 0,\ x\ge\mathbf 0,\ x\neq\mathbf 0
--   \quad\Longleftrightarrow\quad
--   \exists\,y\in\mathbb R^m:\ y^\top A>\mathbf 0^\top . \tag{20}
--   $$
--
--   Inequalities are componentwise; $y^\top A>\mathbf 0^\top$ means every component of $y^\top A$ is strictly positive. Gordan's Theorem characterizes when the homogeneous system $Ax=\mathbf 0$ has no nontrivial nonnegative solution. In the paper it is equivalent to Ville's Theorem (21) and to the minimax theorem (Proposition 4), it follows from Stiemke's Theorem (Proposition 5), and it proves Tucker's Theorem (Theorem 6).
--
--   **Formalization Note** The equivalence is the definition `Gordan20 A`.
--
--   Differences from the source:
--   - encoding: the equivalence (20) → the named proposition `Gordan20 A`; reason: Lean convention so that Theorem 6 can quantify over it; same statement.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Proposition 4, eq. (20), p.9

import Mathlib
import Definitions.Def_StengelZeroSum_Supplement_Gordan20

open Matrix

namespace StengelZeroSum.Supplement

/-- **Gordan's Theorem (20)**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Proposition 4, eq. (20), p.9
("the following Theorem (20) of Gordan"): for every `A ∈ ℝ^{m×n}`,
`∄ x ∈ ℝ^n : Ax = 0, x ≥ 0, x ≠ 0  ⇔  ∃ y ∈ ℝ^m : y⊤A > 0⊤`.

**Formalization Note** The equivalence is the definition `Gordan20 A` (componentwise
inequalities, `y⊤A > 0⊤` strict in every component). `0 < m`, `0 < n` are the standing
assumption (p.4). -/
theorem theorem_20_gordan {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) : Gordan20 A := by sorry

end StengelZeroSum.Supplement
