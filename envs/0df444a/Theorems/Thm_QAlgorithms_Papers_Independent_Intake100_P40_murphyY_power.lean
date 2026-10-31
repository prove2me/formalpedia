-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P40_murphyY_power
-- name    : QAlgorithms.Papers.Independent.Intake100.P40.murphyY_power
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:18:12.219235+00:00
-- url     : https://prove2.me/theorems/7589deea-eb87-4b19-a8ea-1644554057ed
-- title:
--   Colored Jucys–Murphy powers with controlled error
-- statement:
--   Let $R$ be a commutative unital ring, $l\ge1$, $d\ge0$, and work in the truncated skew group algebra $T\rtimes RS_d$, where $T=R[x_1,\ldots,x_d]/(x_1^l,\ldots,x_d^l)$. If $k=(a-1)l+r$ with $a\ge1$ and $0\le r<l$, define
--
--   $$y_i(k)=\sum_{\substack{1\le i_1,\ldots,i_{a-1}<i\\i_1,\ldots,i_{a-1}\text{ distinct}}}(i_1\cdots i_{a-1}i)^{(r)}.$$
--
--   A cycle $A$ of color $r$ means $A^{(r)}=h_r(A)A$ with $h_r(A)$ the truncated complete symmetric sum of degree $(|A|-1)(l-1)+r$. For every $1\le i\le d$ and $p\ge0$,
--
--   $$y_i(l)^p-y_i(pl)\in\operatorname{span}_R\left\{A_1^{(l-1)}\cdots A_m^{(l-1)}:\begin{array}{l}A_1,\ldots,A_m\text{ disjoint cycles in }S_i,\\i\in A_1,\quad |A_1\cup\cdots\cup A_m|\le p\end{array}\right\}.$$
--
--   The family has a distinguished first factor involving $i$. For $p=0$ it is empty and the difference is zero, since $y_i(0)=1$.
--
--   The support bound describes the correction to the leading colored-cycle sum.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, PDF p. 8, Lemma 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- Lemma 2.6, PDF pp.8--9. The difference lies in exactly the stated span;
the error products have a distinguished first cycle involving i. -/
theorem murphyY_power (R : Type*) [CommRing R] (l d : ℕ) (hl : 0 < l)
    (i : Fin d) (p : ℕ) :
    murphyY R l d i l ^ p - murphyY R l d i (p * l) ∈
      Submodule.span R (murphyErrorProducts R l d i p) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P40

end
