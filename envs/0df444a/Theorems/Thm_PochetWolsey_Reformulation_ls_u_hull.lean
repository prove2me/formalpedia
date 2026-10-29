-- Prove2me | Theorems.Thm_PochetWolsey_Reformulation_ls_u_hull
-- name    : PochetWolsey.Reformulation.ls_u_hull
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:51.527716+00:00
-- url     : https://prove2.me/theorems/2879a2dd-43b6-4a8b-be2a-53284399f7e7
-- title:
--   Theorem 7.5 — complete uncapacitated lot-sizing hull
-- statement:
--   Let $n\ge1$ and $d_t\ge0$. Fix $M>0$ with $M\ge\sum_t d_t$. Let $P$ be the continuous relaxation defined by $x_t\in\mathbb R$, $s_t\ge0$, $0\le y_t\le1$, $s_0=s_n=0$, and
--   $$s_{t-1}+x_t=d_t+s_t,\qquad x_t\le My_t.$$
--   Let $X$ be the subset with binary setups. Write $d_{jl}=\sum_{k=j}^l d_k$. Then
--   $$\operatorname{conv}(X)=\left\{(x,s,y)\in P:\ \sum_{j\in S}x_j\le\sum_{j\in S}d_{jl}y_j+s_l\quad\text{for all }1\le l\le n,\ S\subseteq\{1,\ldots,l\}\right\}.$$
--   This is a complete description in the original production, stock, and setup variables, independent of any particular objective.
--
--   **Formalization Note** This is the faithful literal reading of the displayed domain (7.4), which prints $x\in\mathbb R^n$ without a nonnegativity subscript, and defines $X^{LS-U}$ by those constraints on p. 209. It is expected to be disproved: FINDINGS.yaml records the two-period counterexample and the companion corrected item restores $x\ge0$, as in (4.5) and (7.47). The claim is preserved rather than silently repaired. `Fin n` shifts production indices down by one; stocks retain their boundary indices. “Large” $M$ means $M>0$ and $M\ge\sum_t d_t$.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 218 (PDF 232), Theorem 7.5 (compare Theorem 4.2, whose domain explicitly requires nonnegative production); DOI 10.1007/0-387-33477-7

import Mathlib

namespace PochetWolsey.Reformulation

theorem ls_u_hull
    (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (M : ℝ) (hM : 0 < M) (hlarge : (∑ t, d t) ≤ M) :
    let P : Set ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
      {z | z.2.1 0 = 0 ∧ z.2.1 (Fin.last n) = 0 ∧
        (∀ k, 0 ≤ z.2.1 k) ∧
        (∀ t, 0 ≤ z.2.2 t ∧ z.2.2 t ≤ 1 ∧
          z.2.1 t.castSucc + z.1 t = d t + z.2.1 t.succ ∧
          z.1 t ≤ M * z.2.2 t)}
    let X := {z | z ∈ P ∧ ∀ t, z.2.2 t = 0 ∨ z.2.2 t = 1}
    convexHull ℝ X =
      {z | z ∈ P ∧ ∀ (l : Fin n) (S : Finset (Fin n)),
        (∀ j ∈ S, j ≤ l) →
          (∑ j ∈ S, z.1 j) ≤
            (∑ j ∈ S, (∑ k ∈ Finset.Icc j l, d k) * z.2.2 j) + z.2.1 l.succ} := by sorry

end PochetWolsey.Reformulation
