-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_lemma_3_8
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.lemma_3_8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:51:22.937831+00:00
-- url     : https://prove2.me/theorems/26c0e9ba-bae7-49b3-bad6-6c2194980777
-- title:
--   Lemma 3.8
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   In either presentation, for $1\le i<n$,
--   $$g_i^2=1+\lambda^{-1}ze_i-zg_i,\qquad g_i^{-2}=1-\lambda ze_i+zg_i^{-1}.$$
--   These are the quadratic consequences of the skein relation. The inverse-square formula corrects the printed final $zg_i$ using the source's prescribed multiplication by $g_i^{-1}$.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 18, Lemma 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Lemma 3.8, PDF p.18, in both ordinary and affine BMW algebras.
Source correction: the printed final z*g_i is z*g_i inverse, as follows
by multiplying the skein relation by g_i inverse. Independent moderation
of this correction remains required. -/
theorem lemma_3_8 (aff : Bool) (n i : ℕ) (hi : BMWIndex n i) :
    ghCrossing P q aff n i false ^ 2 = 1 +
      algebraMap R _ ((↑P.lam⁻¹ : R) * P.z) * ghContraction P q aff n i -
      algebraMap R _ P.z * ghCrossing P q aff n i false ∧
    ghCrossing P q aff n i true ^ 2 = 1 -
      algebraMap R _ ((P.lam : R) * P.z) * ghContraction P q aff n i +
      algebraMap R _ P.z * ghCrossing P q aff n i true := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
