-- Prove2me | Theorems.Thm_StengelZeroSum_relaxation_least_eq
-- name    : StengelZeroSum.relaxation_least_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:05:10.53399+00:00
-- url     : https://prove2.me/theorems/4d20a424-7bff-4b64-bc05-2286171e2bcd
-- title:
--   Proof of Theorem 7 — the least slack $w$ in (53) is $w^*$ when $w^*>0$
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$, let $C$, $d$ be as in (57), and let $(z^*,w^*)$ minimize $w$ subject to (58). If $w^*>0$, then $w^*$ is the smallest real $w$ such that
--
--   $$
--   A\bar x\le b+\mathbf1w,\qquad \bar x\ge\mathbf0,\qquad -A^\top\bar y\le-c+\mathbf1w,\qquad \bar y\ge\mathbf0\qquad(53)
--   $$
--
--   has feasible solutions $\bar x$, $\bar y$.
--
--   For $C$, $d$ of (57), the system (58) is (53) together with the extra constraints $b^\top\bar y-c^\top\bar x\le w$ and $w\ge0$. The paper's proof of Theorem 7 derives part (b) "via (72)", which gives (54) only once the minimal $w$ of (53) is known to coincide with $w^*$; this item states that step.
--
--   **Formalization Note** "Smallest" is a least element, so the minimum is attained.
--
--   Differences from the source:
--   - reading: 'This shows part (a) in Theorem 7, and also part (b) via (72)' → the least w for which (53) is feasible equals w* whenever w* > 0; reason: (72) is a formula for w* of (58), while (54) is about (53); the sentence relies on this equality, which the page leaves unstated
--   - generalization: (z*, w*) a basic feasible minimizer of (58) → (z*, w*) any minimizer of (58); reason: the equality concerns only the optimal value w*; basic minimizers are a special case
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, proof of Theorem 7, p.23

import Mathlib
import Definitions.Def_StengelZeroSum_C57
import Definitions.Def_StengelZeroSum_d57
import Definitions.Def_StengelZeroSum_IsMin58
import Definitions.Def_StengelZeroSum_Feasible53

open Matrix

namespace StengelZeroSum

/-- **The least relaxation `w` of (53) is the optimal `w*` of (58)**,
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, proof of
Theorem 7, p.23 ("This shows part (a) in Theorem 7, and also part (b) via (72)").

Let `C`, `d` be as in (57) and let `(z*, w*)` minimize `w` subject to (58). If `w* > 0`, then
`w*` is the smallest `w` for which (53)
`Ax̄ ≤ b + 1w, x̄ ≥ 0, −A⊤ȳ ≤ −c + 1w, ȳ ≥ 0` has feasible solutions.

**Formalization Note** The page leaves this step implicit: (58) for (57) is (53) with the extra
constraints `b⊤y − c⊤x ≤ w` and `w ≥ 0`, and (54) follows from (72) only once the two minima are
known to agree when `w* > 0`. `m, n > 0` is the paper's standing assumption (p.4). -/
theorem relaxation_least_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (zs : Fin m ⊕ Fin n → ℝ) (ws : ℝ) (hmin : IsMin58 (C57 A) (d57 b c) zs ws) (hpos : 0 < ws) :
    IsLeast {w : ℝ | Feasible53 A b c w} ws := by sorry

end StengelZeroSum
