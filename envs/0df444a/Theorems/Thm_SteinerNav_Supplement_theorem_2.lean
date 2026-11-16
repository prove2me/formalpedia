-- Prove2me | Theorems.Thm_SteinerNav_Supplement_theorem_2
-- name    : SteinerNav.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:13:11.18567+00:00
-- url     : https://prove2.me/theorems/0a26c158-a1d2-4d89-aa21-15bab476a391
-- title:
--   Theorem 2 — main lower bound $\Omega(n^2\log n/(d\log d))$ edges for $\alpha\ge1+c\log n/d$, on point sets of aspect ratio $O(d/\log n)$
-- statement:
--   There are absolute constants $c,A,B>0$ with the following property. For every $n\ge2$, every dimension $d$ with $d\ge c\ln n$ and every $\alpha\ge 1+c\ln n/d$, there is a set $P$ of exactly $n$ points of $\mathbb R^d$ with aspect ratio
--   $$\Delta(P)\le A\,\frac{d}{\ln n}$$
--   such that every $\alpha$-navigable graph with Steiner points on $P$ (Definition 1: any finite set $R\subset\mathbb R^d\setminus P$ of Steiner points and any edge set on $P\cup R$ in which every vertex $s$ has, for each target $t\in P\setminus\{s\}$, an out-neighbor $v$ with $\|v-t\|<\|s-t\|/\alpha$) has at least
--   $$B\,\frac{n^2\ln n}{d\ln d}$$
--   edges.
--
--   This is the paper's main lower bound: for subpolynomial dimension it shows that the choice $\alpha-1=1/d$ of the upper bound (Theorem 1) is tight up to an $O(\log n)$ factor among constructions with $n^{2-\Omega(1)}$ edges, and that the lower bound does not come from a large aspect ratio.
--
--   **Formalization Note** The constant $c$ and the constants hidden in $O(d/\log n)$ and $\Omega(n^2\log n/(d\log d))$ are made explicit as $c,A,B$ and quantified before $n$, $d$ and $\alpha$. The aspect ratio is the published `SteinerNav.aspectRatio` (largest over smallest pairwise distance), and navigability is the published `SteinerNav.IsSteinerNavigable`.
--
--   Differences from the source:
--   - reading: "there is a constant c", aspect ratio "O(d/log n)", "Ω(n² log n/(d log d)) edges" → explicit absolute constants c, A, B > 0 quantified before n, d, α; reason: the standard meaning of the asymptotic notation with constants independent of n, d, α, P and the graph (the proof gives c = 256, A = 1/64, B = 1/32).
--   - reading: n unrestricted → n ≥ 2; reason: at n = 1 the expressions log n and c log n/d degenerate (aspect ratio bound d/log 1 undefined); the proof covers even n ≥ 4 and odd n ≥ 5, and n = 2, 3 hold with small constants.
--   - encoding: log → natural logarithm ln; reason: a change of base is absorbed by the constants c, A, B.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee62135a42ef49d815773f6af7f50ba344b9460d6007d849529b707b183), Theorem 2, p.3 (PDF p.3), restated p.15 (PDF p.15); proof §5.3, pp.16–17

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_aspectRatio

namespace SteinerNav.Supplement

/-- Theorem 2 (main lower bound): there are absolute constants `c, A, B > 0` such that for every
`n ≥ 2`, every dimension `d ≥ c ln n` and every `α ≥ 1 + c ln n/d` there is a set `P` of exactly `n`
points of `ℝ^d` with aspect ratio at most `A d/ln n` such that every `α`-navigable graph with Steiner
points on `P` has at least `B n² ln n/(d ln d)` edges (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 2, p.3, restated p.15; proof §5.3, pp.16–17).

**Formalization Note** The constant `c` and the constants `A`, `B` hidden in `O(d/log n)` and
`Ω(n² log n/(d log d))` are absolute: they come before `n`, `d`, `α`. Logarithms are natural. `α` has
no upper bound. "Every graph" ranges over every finite set `R` of Steiner points and every edge set
`E` with `IsSteinerNavigable α P R E` (Definition 1). -/
theorem theorem_2 : ∃ c A B : ℝ, 0 < c ∧ 0 < A ∧ 0 < B ∧
    ∀ n d : ℕ, 2 ≤ n → c * Real.log n ≤ (d : ℝ) →
    ∀ α : ℝ, 1 + c * Real.log n / (d : ℝ) ≤ α →
    ∃ P : Finset (Pt d), P.card = n ∧
      aspectRatio P ≤ A * (d : ℝ) / Real.log n ∧
      ∀ (R : Finset (Pt d)) (E : Finset (Pt d × Pt d)), IsSteinerNavigable α P R E →
        B * (n : ℝ) ^ 2 * Real.log n / ((d : ℝ) * Real.log d) ≤ (E.card : ℝ) := by sorry

end SteinerNav.Supplement
