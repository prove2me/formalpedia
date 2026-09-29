-- Prove2me | Theorems.Thm_RHLinalg_sum_sq_diff_lower
-- name    : RHLinalg.sum_sq_diff_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:38:48.988389+00:00
-- url     : https://prove2.me/theorems/1d112163-5786-4524-873c-e03dab58b138
-- title:
--   Sum estimate A: $\sum (p_i - m_i)^2 \ge c \sum p_i - \tfrac{c^2}{4} r - 2c \sum m_i$
-- statement:
--   Let $\iota$ be a finite index type, $p, m : \iota \to \mathbb{R}$ with $m_i \ge 0$ for all $i$, and suppose the number of indices where $p_i \ne 0$ is at most $r \in \mathbb{N}$. Let $c \ge 0$ be real.
--
--   **Statement.**
--   $$c \sum_i p_i \;-\; \frac{c^2}{4}\, r \;-\; 2c \sum_i m_i \;\le\; \sum_i (p_i - m_i)^2 .$$
--
--   This elementary inequality is the first of the two scalar estimates in the proof of the rank–trace inequality (paper reference `lem:ranktrace`); pointwise it amounts to $(p - m)^2 \ge c\,p - c^2/4 - 2c\,m$ for $m \ge 0$, applied only at the at most $r$ indices where $p_i \ne 0$ and summed. In the module `Zeta23.LinAlg.RankTrace` it is consumed directly by `RHLinalg.rank_trace_ineq`, where $p$ plays the role of the eigenvalues of the positive semidefinite matrix $P$ (nonzero at most $\operatorname{rank} P$ times) and $m$ the negative parts of the eigenvalues of $Q$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/RankTrace.lean#L59-L83, docstring tag [lem:ranktrace]

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef

open Matrix Finset
open scoped ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem RHLinalg.sum_sq_diff_lower {p m : ι → ℝ} (hm : ∀ i, 0 ≤ m i)
    {r : ℕ} (hr : #{i | p i ≠ 0} ≤ r) {c : ℝ} (hc : 0 ≤ c) :
    c * (∑ i, p i) - c ^ 2 / 4 * r - 2 * c * (∑ i, m i) ≤ ∑ i, (p i - m i) ^ 2 := by sorry
