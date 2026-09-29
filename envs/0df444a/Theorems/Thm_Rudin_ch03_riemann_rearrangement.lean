-- Prove2me | Theorems.Thm_Rudin_ch03_riemann_rearrangement
-- name    : Rudin.ch03_riemann_rearrangement
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:32:55.227236+00:00
-- url     : https://prove2.me/theorems/ad6827c3-2d91-4b12-8ce1-86646847d1aa
-- title:
--   Theorem 3.54 — Riemann's rearrangement theorem
-- statement:
--   Let $\sum a_n$ be a series of real numbers which converges but not absolutely, and let $-\infty \le \alpha \le \beta \le +\infty$. Then there is a rearrangement $\sum a_{\sigma(n)}$, $\sigma$ a bijection of $\mathbb{N}$, whose partial sums $s_n'$ satisfy $\liminf_n s_n' = \alpha$ and $\limsup_n s_n' = \beta$. In particular a conditionally convergent series can be rearranged to converge to any prescribed real value, or to diverge.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 76, Definition 3.52 and Theorem 3.54

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.54 (Riemann's rearrangement theorem): let `∑ aₙ` be a series of real
numbers which converges but not absolutely, and let `-∞ ≤ α ≤ β ≤ ∞`.  Then there is a
rearrangement `∑ a_{σ(n)}` whose partial sums `sₙ'` satisfy `liminf sₙ' = α` and
`limsup sₙ' = β`. -/
theorem ch03_riemann_rearrangement (a : ℕ → ℝ)
    (hconv : SeriesConverges a) (hnabs : ¬ SeriesConvergesAbsolutely a)
    (α β : EReal) (hαβ : α ≤ β) :
    ∃ σ : Equiv.Perm ℕ,
      liminf (fun n => ((partialSum (fun k => a (σ k)) n : ℝ) : EReal)) atTop = α ∧
      limsup (fun n => ((partialSum (fun k => a (σ k)) n : ℝ) : EReal)) atTop = β := by sorry

end Rudin
