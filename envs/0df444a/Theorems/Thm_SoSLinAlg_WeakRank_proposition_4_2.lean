-- Prove2me | Theorems.Thm_SoSLinAlg_WeakRank_proposition_4_2
-- name    : SoSLinAlg.WeakRank.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:31:47.702871+00:00
-- url     : https://prove2.me/theorems/eacbd0fb-c8c3-4964-ac2a-2576a4813c10
-- title:
--   Proposition 4.2 — ideal membership with the full degree bound
-- statement:
--   Let $n>r\ge1$ and $0\le d\le r$ be integers, and let $X,Y$ be $n\times r$ matrices of real indeterminates. Let $Z_d$ be the real locus $XY^\top=0$, $\operatorname{rank}X+\operatorname{rank}Y\le d$.
--
--   If $f\in\mathbb R[X,Y]$ has degree at most $d$ and vanishes on $Z_d$, then there exist polynomials $h_{ij}$ such that
--   $$f=\sum_{i,j=1}^n h_{ij}(XY^\top)_{ij},\qquad \deg h_{ij}\le d-2\quad\text{for all }i,j.$$
--   The degree of the zero polynomial in this display is $-\infty$. Thus when $d=0$ or $d=1$, all multipliers and $f$ are zero.
--
--   This is degree-controlled membership in the ideal of the entries of $XY^\top$. Vanishing is required on exactly the real rank-bounded locus, not a smaller collection of row-supported points. No ideal-membership hypothesis is assumed.
--
--   Differences from the source:
--   - encoding: matrix entries indexed by [n] and [r] → entries indexed by Fin n and Fin r, and equations by pairs of indices; reason: zero-based finite indices enumerate precisely the same entries and equations
--   - encoding: the zero polynomial has degree minus infinity in the bound deg f ≤ d → f.totalDegree ≤ d with totalDegree 0 = 0; reason: d is nonnegative, so the allowed f are unchanged; the possibly negative multiplier bound is encoded separately
--   - encoding: Z_d is introduced for positive d but the propositions allow d = 0 → Z is defined for every natural d, including Z_0; reason: the source explicitly uses Z_0 = {(0,0)} in its proof, PDF p.18
--   - encoding: degree h_ij at most d - 2, with degree(0) = minus infinity → h_ij = 0 or totalDegree(h_ij) + 2 ≤ d; reason: equivalent for every natural d; for d = 0 or 1 it forces every multiplier to be zero
-- source:
--   Dmitriy Kunisky, Xifan Yu, The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission #1181 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf, Proposition 4.2, PDF p.15 (printed p.13); endpoint explanation PDF p.17 (printed p.15)

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_Z

namespace SoSLinAlg.WeakRank

/-- Proposition 4.2, PDF p.15 (printed p.13). The disjunction implements
 degree(0) = -∞; at d = 0 or 1 every multiplier must be zero. -/
theorem proposition_4_2 {n r d : ℕ} (hr : 0 < r) (hrn : r < n) (hdr : d ≤ r)
    (f : Poly n r) (hf : f.totalDegree ≤ d) (hvan : VanishesOnZ d f) :
    ∃ h : (Fin n × Fin n) → Poly n r,
      f = ∑ ij, h ij * xy ij.1 ij.2 ∧
      ∀ ij, h ij = 0 ∨ (h ij).totalDegree + 2 ≤ d := by sorry

end SoSLinAlg.WeakRank
