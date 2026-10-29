-- Prove2me | Theorems.Thm_PochetWolsey_Reformulation_ls_inequality_valid
-- name    : PochetWolsey.Reformulation.ls_inequality_valid
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:43.976679+00:00
-- url     : https://prove2.me/theorems/1c05f7a2-3767-4962-9c6a-bb93075eaf8b
-- title:
--   Proposition 7.4 — validity of the $(l,S)$ inequalities
-- statement:
--   Let $n\ge1$, $d_t\ge0$, and let $(x,s,y)$ be a feasible uncapacitated lot-sizing plan: production is real-valued and stock is nonnegative, initial and final stocks are zero, setups are binary, $s_{t-1}+x_t=d_t+s_t$, and $x_t\le My_t$ for a positive $M\ge\sum_t d_t$. For $1\le l\le n$, put $L=\{1,\ldots,l\}$ and take any $S\subseteq L$. With $d_{jl}=\sum_{k=j}^l d_k$, the inequality
--   $$\sum_{j\in S}x_j\le\sum_{j\in S}d_{jl}y_j+s_l$$
--   is valid for every such plan. These inequalities constrain the interaction between production and setup decisions over each prefix of the horizon.
--
--   **Formalization Note** This is the faithful literal reading of the displayed domain (7.4), which prints $x\in\mathbb R^n$ without a nonnegativity subscript, and defines $X^{LS-U}$ by those constraints on p. 209. It is expected to be disproved: FINDINGS.yaml records the two-period counterexample and the companion corrected item restores $x\ge0$, as in (4.5) and (7.47). The claim is preserved rather than silently repaired. `Fin n` shifts production indices down by one; stocks retain their boundary indices. “Large” $M$ means $M>0$ and $M\ge\sum_t d_t$.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 218 (PDF 232), Proposition 7.4, Eq. (7.10); DOI 10.1007/0-387-33477-7

import Mathlib

namespace PochetWolsey.Reformulation

theorem ls_inequality_valid
    (n : ℕ) (hn : 0 < n) (d x y : Fin n → ℝ) (s : Fin (n + 1) → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hs : ∀ k, 0 ≤ s k)
    (hstart : s 0 = 0) (hend : s (Fin.last n) = 0)
    (hy : ∀ t, y t = 0 ∨ y t = 1)
    (hbalance : ∀ t, s t.castSucc + x t = d t + s t.succ)
    (M : ℝ) (hM : 0 < M) (hlarge : (∑ t, d t) ≤ M)
    (hsetup : ∀ t, x t ≤ M * y t)
    (l : Fin n) (S : Finset (Fin n)) (hS : ∀ j ∈ S, j ≤ l) :
    (∑ j ∈ S, x j) ≤
      (∑ j ∈ S, (∑ k ∈ Finset.Icc j l, d k) * y j) + s l.succ := by sorry

end PochetWolsey.Reformulation
