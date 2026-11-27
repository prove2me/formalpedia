-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_tucker_theorem_39
-- name    : StengelZeroSum.Supplement.tucker_theorem_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:29:34.040344+00:00
-- url     : https://prove2.me/theorems/c44620bb-e86a-400f-b308-e911cb4f50b4
-- title:
--   Tucker's Theorem (39) — some $y,x$ have $y^\top A\ge0^\top$, $x\ge0$, $Ax=0$, $x^\top+y^\top A>0^\top$
-- statement:
--   Let $A$ be a real $m\times n$ matrix ($m,n\ge1$). Then there exist $y\in\mathbb R^m$ and $x\in\mathbb R^n$ with
--
--   $$
--   y^\top A\ge\mathbf 0^\top,\qquad x\ge\mathbf 0,\qquad Ax=\mathbf 0,\qquad x^\top+y^\top A>\mathbf 0^\top . \tag{39}
--   $$
--
--   Inequalities are componentwise; the last condition says $x_j+(y^\top A)_j>0$ for every column $j$. Tucker's Theorem is a strict-complementarity theorem of the alternative: it proves Gordan's and Stiemke's Theorems, the Lemma of Farkas, and strict complementarity in linear programming (Proposition 10).
--
--   **Formalization Note** The conclusion is the definition `Tucker39 A`.
--
--   Differences from the source:
--   - encoding: the conclusion (39) → the named proposition `Tucker39 A`; reason: Lean convention shared with Theorem 6; same statement.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Proposition 9, eq. (39), p.15

import Mathlib
import Definitions.Def_StengelZeroSum_Supplement_Tucker39

open Matrix

namespace StengelZeroSum.Supplement

/-- **Tucker's Theorem (39)**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Proposition 9, eq. (39), p.15 ("Tucker's Theorem"):
for every `A ∈ ℝ^{m×n}`,
`∃ y ∈ ℝ^m, x ∈ ℝ^n : y⊤A ≥ 0⊤, x ≥ 0, Ax = 0, x⊤ + y⊤A > 0⊤`.

**Formalization Note** The conclusion is the definition `Tucker39 A` (componentwise
inequalities; `x⊤ + y⊤A > 0⊤` strict in every component). `0 < m`, `0 < n` are the standing
assumption (p.4). -/
theorem tucker_theorem_39 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) : Tucker39 A := by sorry

end StengelZeroSum.Supplement
