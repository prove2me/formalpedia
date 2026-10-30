-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P24_consecutive_column_annihilation
-- name    : QAlgorithms.Papers.Independent.Extend50.P24.consecutive_column_annihilation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:48:14.825706+00:00
-- url     : https://prove2.me/theorems/688784c5-43e6-464f-a961-ddadcec2b947
-- title:
--   Consecutive-label column collision annihilates the subgroup sum
-- statement:
--   Let $T$ be a standard Young tableau of shape $\lambda$ with labels $1,\ldots,n$, and let $\rho_\lambda$ be the Young orthonormal representation specified by (2.5)–(2.8). Let $A\subseteq\{1,\ldots,n\}$ consist of consecutive integers. Write $S_A$ for all permutations of $A$, extended to fix every label outside $A$.
--
--   If two distinct labels in $A$ occupy the same column of $T$, then the unnormalized subgroup sum satisfies
--
--   $$
--   \left(\sum_{\pi\in S_A}\rho_\lambda(\pi)\right)|T\rangle=0.
--   $$
--
--   The conclusion is only the stated annihilation direction. The collision premise cannot hold when $|A|<2$; no additional positive-size hypothesis is needed. The tableau ket is the normalized computational basis vector in the actual SYT coordinate space.
--
--   This is the column-collision lemma used in the permutation-module discussion, independent of the disputed multiplicity-basis compression. **Formalization Note.** Labels are shifted to $\operatorname{Fin}(n)$, and the subgroup sum has no factor $|S_A|^{-1}$.
-- source:
--   An efficient high dimensional quantum Schur transform, arXiv:1804.00055v2, PDF p. 15, Lemma 2: consecutive-label subgroup symmetrizer annihilates a column collision

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P24

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Extend50.P24

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P26 (boxContent)

/-- Lemma 2, PDF pp.15-16: any two distinct consecutive-set labels in the
same column force the unnormalized subgroup sum to annihilate that SYT.
The premise is one-way; no false support-iff or SSYT-basis claim is included. -/
theorem consecutive_column_annihilation
    {n : ℕ} {lambda : YoungDiagram} (Y : YoungModel n lambda)
    (A : Finset (Fin n)) (hA : IsConsecutive A) (T : StandardTableau n lambda)
    (hcollision : ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ (T.val i).val.2 = (T.val j).val.2) :
    QAlgorithms.act (subgroupSum Y A) (QAlgorithms.ket T) = 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P24

end
