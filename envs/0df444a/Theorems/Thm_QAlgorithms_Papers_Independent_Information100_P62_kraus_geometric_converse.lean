-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_kraus_geometric_converse
-- name    : QAlgorithms.Papers.Independent.Information100.P62.kraus_geometric_converse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:38:45.674534+00:00
-- url     : https://prove2.me/theorems/b62fa5cf-11c9-4ef2-961e-68aa902069ce
-- title:
--   Lemma 3.8: Kraus-geometric converse bounds
-- statement:
--   Let $\Phi(X)=\sum_iE_iXE_i^*$ be a channel and let $A=\bigoplus_kM_{d_k}(\mathbb C)$ be transmittable. There are Kraus labels $i_k$, with repetitions allowed, such that, for disjoint label sets $U,J$ and $V_B=\operatorname{span}_{k\in B}\operatorname{im}E_{i_k}$,
--   $$\sum_{k\in J}d_k\le\dim V_J-[\dim(\Pi_{V_U}V_J)-\dim V_U+\sum_{k\in U}d_k]_+.$$
--   Also $\max_kd_k\le\max_i\operatorname{rank}E_i$, and for each integer $t\ge1$, $\sum_{d_k\ge t}d_k\le\dim\operatorname{span}_{\operatorname{rank}E_i\ge t}\operatorname{im}E_i\le\sum_{\operatorname{rank}E_i\ge t}\operatorname{rank}E_i$. The full output span is $\operatorname{supp}\Phi(I)$. These are code-independent converse bounds.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 25, Lemma 3.8: Kraus-geometric converse bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.25, 26, 27, Lemma 3.8: Kraus-geometric converse bounds. -/
theorem kraus_geometric_converse [Nonempty I] [Nonempty O]
    {r : ℕ} (E : Fin r → Matrix O I ℂ) (hE : IsKrausFamily E)
    (A : Shape) (hA : Transmits (krausApply E) A) :
    (∃ f : Block A → Fin r, ∀ U V : Finset (Block A), Disjoint U V →
      (∑ k ∈ V, (blockSize A k : ℤ)) +
        max 0 ((Module.finrank ℂ ((selectedSpan E f V).map
          (Matrix.toEuclideanLin (projection (selectedSpan E f U)))) : ℤ) -
          Module.finrank ℂ (selectedSpan E f U) + ∑ k ∈ U, (blockSize A k : ℤ)) ≤
        Module.finrank ℂ (selectedSpan E f V)) ∧
    (∀ k : Block A, blockSize A k ≤ univ.sup (fun i => (E i).rank)) ∧
    (∀ t : ℕ, 1 ≤ t →
      (∑ k ∈ univ.filter (fun k => t ≤ blockSize A k), blockSize A k) ≤
        Module.finrank ℂ (⨆ i : {i : Fin r // t ≤ (E i).rank}, imageSpace (E i.val) :
          Submodule ℂ (EuclideanSpace ℂ O)) ∧
      Module.finrank ℂ (⨆ i : {i : Fin r // t ≤ (E i).rank}, imageSpace (E i.val) :
          Submodule ℂ (EuclideanSpace ℂ O)) ≤
        ∑ i ∈ univ.filter (fun i => t ≤ (E i).rank), (E i).rank) ∧
    (⨆ i : Fin r, imageSpace (E i)) = imageSpace (krausApply E 1) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
