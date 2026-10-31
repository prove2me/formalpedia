-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P54_skewTableaux_chambers
-- name    : QAlgorithms.Papers.Independent.Intake100.P54.skewTableaux_chambers
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:47:39.50843+00:00
-- url     : https://prove2.me/theorems/c1dfeea3-a815-4048-9e99-985d4a76f32e
-- title:
--   Theorem 5.9: skew-shape standard tableaux biject with chambers
-- statement:
--   Let $S=\lambda/\mu$ be a skew diagram with $n$ boxes, placed on integer-labelled diagonals. Number its boxes $b_1,\ldots,b_n$ by increasing diagonal content and, on a diagonal, from northwest to southeast. Write $\gamma_i=c(b_i)$ and let $J$ consist of the roots $\varepsilon_j-\varepsilon_i$ with $i<j$, $c(b_j)-c(b_i)=1$, and $b_j$ strictly north and weakly west of $b_i$. Let $\mathcal F^S$ be the bijective fillings by $1,\ldots,n$ increasing along rows and down columns. For a permutation $w$, let $R(w)=\{\varepsilon_j-\varepsilon_i:i<j,\ w(j)<w(i)\}$, and put $Z(\gamma)=\{\alpha>0:\langle\gamma,\alpha\rangle=0\}$ and $P(\gamma)=\{\alpha>0:\langle\gamma,\alpha\rangle=1\}$. Then the specified word map is a bijection:
--
--   $$\mathcal F^S\longrightarrow\{w\in S_n:R(w)\cap Z(\gamma)=\varnothing,\ R(w)\cap P(\gamma)=J\},\qquad p\longmapsto(p(b_1),\ldots,p(b_n)).$$
--
--   This identifies ordinary standard skew tableaux with the chamber labels used in the paper. Arbitrary integer shifts of placement and the empty diagram are included.
-- source:
--   Affine Hecke algebras and generalized standard Young tableaux, arXiv:math/0401329v2, PDF p. 24, Theorem 5.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P54

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P54

/-- Theorem 5.9, PDF p.24 (definitions pp.22–25): the word map is a
bijection from independently defined row/column standard skew tableaux to
the chamber set. The final equation specifies the map, not just equal
cardinalities or an arbitrary equivalence. Integer placements and n=0 are
included. -/
theorem skewTableaux_chambers {n : ℕ} (S : PlacedSkewShape n) :
    ∃ e : SkewTableaux S ≃
      {w : Equiv.Perm (Fin n) //
        w ∈ aRegion (fun i => (S.gamma i : ℝ)) S.J},
      ∀ p : SkewTableaux S, (e p).val = tableauWord p.val := by sorry

end QAlgorithms.Papers.Independent.Intake100.P54

end
