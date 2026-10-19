-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_tvec_cvec1
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.tvec_cvec1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:56:31.061988+00:00
-- url     : https://prove2.me/theorems/86714dd6-e5b1-4463-90b5-34dc1ebbd772
-- title:
--   §5.3.3, Lemma tvec_cvec1
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For a finite list $z$ and polynomial $Q$, form rational row vectors $t=(\operatorname{TaQ}(z,Q),\operatorname{TaQ}(z,Q^2),\operatorname{TaQ}(z,1))$ and $c=(c_1,c_{-1},c_0)$, where $c_s$ counts sign $s$. With
--
--   $$M=\begin{pmatrix}1&1&1\\-1&1&1\\0&0&1\end{pmatrix},\qquad t=cM.$$
--
--   The order of signs, powers, and matrix multiplication agrees with the displayed source system.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 26, §5.3.3, Lemma tvec_cvec1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 26, tvec_cvec1, preserving row-vector orientation. -/
theorem tvec_cvec1 {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (z : List R) (q : Polynomial R) :
    tvec1 z q = Matrix.vecMul (cvec1 z q) ctmat1 := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
