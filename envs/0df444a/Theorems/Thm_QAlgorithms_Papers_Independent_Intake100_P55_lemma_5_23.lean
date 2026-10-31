-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_lemma_5_23
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.lemma_5_23
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:58:30.85288+00:00
-- url     : https://prove2.me/theorems/060f51a8-22ef-4c8e-ac1a-ba372fbb5865
-- title:
--   Lemma 5.23
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   Let $k\ge0$ and work in any ordinary level $W_n$ with $2k<n$. Put $O_k=e_1e_3\cdots e_{2k-1}$ and $H_k=e_2e_4\cdots e_{2k}$, interpreting an empty product as $1$. Then
--   $$(g_1\cdots g_{2k})O_k=H_kO_k,\qquad O_k(g_{2k}\cdots g_1)=O_kH_k.$$
--   These product identities replace consecutive braid generators by even contractions.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 40, Lemma 5.23

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Lemma 5.23, PDF p.40, in any ordinary ambient bmwLevel containing the
largest generator 2k. At k=0 both identities are empty products. -/
theorem lemma_5_23 (n k : ℕ) (hn : 2*k < n) :
    let g := fun i => ghCrossing P q false n i false
    let e := ghContraction P q false n
    let odd := oddContractions P q n k
    let even := ((List.range k).map fun j => e (2*j+2)).prod
    forward g 1 (2*k) * odd = even * odd ∧
    odd * backward g 1 (2*k) = odd * even := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
