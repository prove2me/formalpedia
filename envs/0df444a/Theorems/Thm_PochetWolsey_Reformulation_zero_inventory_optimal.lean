-- Prove2me | Theorems.Thm_PochetWolsey_Reformulation_zero_inventory_optimal
-- name    : PochetWolsey.Reformulation.zero_inventory_optimal
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:41.691142+00:00
-- url     : https://prove2.me/theorems/36a6bfa0-214f-41bc-8f9f-5e1450460852
-- title:
--   Proposition 7.1 — zero-inventory optimal production plan
-- statement:
--   Consider a finite horizon of $n\ge1$ periods, nonnegative demands $d_t$, arbitrary real unit production costs $p_t$, stock costs $h_t$, and setup costs $q_t$. Let $M>0$ satisfy $M\ge\sum_t d_t$. The feasible set $X$ consists of real production $x_t$ and nonnegative stocks $s_t$, binary setups $y_t$, zero initial and final stocks, and
--   $$s_{t-1}+x_t=d_t+s_t,\qquad x_t\le My_t.$$
--   There is a feasible plan minimizing $\sum_t p_tx_t+\sum_{t=0}^n h_ts_t+\sum_t q_ty_t$ over all of $X$ such that
--   $$s_{t-1}x_t=0\qquad(t=1,\ldots,n).$$
--   Thus at least one optimal plan produces only when its entering inventory is zero. Setups without production remain permitted, including when setup costs are negative.
--
--   **Formalization Note** This is the faithful literal reading of the displayed domain (7.4), which prints $x\in\mathbb R^n$ without a nonnegativity subscript, and defines $X^{LS-U}$ by those constraints on p. 209. It is expected to be disproved: FINDINGS.yaml records the two-period counterexample and the companion corrected item restores $x\ge0$, as in (4.5) and (7.47). The claim is preserved rather than silently repaired. `Fin n` shifts production indices down by one; stocks retain their boundary indices. “Large” $M$ means $M>0$ and $M\ge\sum_t d_t$.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 210 (PDF 224), Proposition 7.1; model (7.1)–(7.6); DOI 10.1007/0-387-33477-7

import Mathlib

namespace PochetWolsey.Reformulation

theorem zero_inventory_optimal
    (n : ℕ) (hn : 0 < n) (d p q : Fin n → ℝ) (h : Fin (n + 1) → ℝ)
    (hd : ∀ t, 0 ≤ d t) (M : ℝ) (hM : 0 < M) (hlarge : (∑ t, d t) ≤ M) :
    let P : Set ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
      {z | z.2.1 0 = 0 ∧ z.2.1 (Fin.last n) = 0 ∧
        (∀ k, 0 ≤ z.2.1 k) ∧
        (∀ t, 0 ≤ z.2.2 t ∧ z.2.2 t ≤ 1 ∧
          z.2.1 t.castSucc + z.1 t = d t + z.2.1 t.succ ∧
          z.1 t ≤ M * z.2.2 t)}
    let X := {z | z ∈ P ∧ ∀ t, z.2.2 t = 0 ∨ z.2.2 t = 1}
    let cost := fun z : (Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (∑ t, p t * z.1 t) + (∑ k, h k * z.2.1 k) + (∑ t, q t * z.2.2 t)
    ∃ z ∈ X, (∀ z' ∈ X, cost z ≤ cost z') ∧
      ∀ t, z.2.1 t.castSucc * z.1 t = 0 := by sorry

end PochetWolsey.Reformulation
