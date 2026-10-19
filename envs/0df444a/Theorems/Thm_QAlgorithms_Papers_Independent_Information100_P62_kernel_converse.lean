-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_kernel_converse
-- name    : QAlgorithms.Papers.Independent.Information100.P62.kernel_converse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:41:11.916191+00:00
-- url     : https://prove2.me/theorems/78a18697-0275-4ed7-9455-cc07296672e8
-- title:
--   Lemma 3.12: kernel converse
-- statement:
--   For every nonzero quantum code $C$ of $\Phi$,
--   $$C\subseteq\bigcap_{X\in S_\Phi,\ X\ge0,\ \operatorname{rank}X<\dim C}\ker X.$$
--   Consequently, if $\bigoplus_kM_{d_k}(\mathbb C)$ is transmittable and $t\ge1$, then
--   $$\sum_{d_k\ge t}d_k\le\dim\bigcap_{X\in S_\Phi,\ X\ge0,\ \operatorname{rank}X<t}\ker X\le\dim\bigcap_{\operatorname{rank}E_i<t}\ker E_i.$$
--   Empty intersections mean the full input space. The strict rank thresholds are essential.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 28, Lemma 3.12: kernel converse

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.28, Lemma 3.12: kernel converse. -/
theorem kernel_converse [Nonempty I] [Nonempty O]
    {r : ℕ} (E : Fin r → Matrix O I ℂ) (hE : IsKrausFamily E) :
    (∀ C : Submodule ℂ (EuclideanSpace ℂ I), 0 < Module.finrank ℂ C →
      Code (graph (krausApply E)) (projection C) →
      C ≤ ⨅ X : {X : Matrix I I ℂ // X ∈ graph (krausApply E) ∧ X.PosSemidef ∧ X.rank < Module.finrank ℂ C},
        kernelSpace X.val) ∧
    ∀ A : Shape, Transmits (krausApply E) A → ∀ t : ℕ, 1 ≤ t →
      (∑ k ∈ univ.filter (fun k => t ≤ blockSize A k), blockSize A k) ≤
        Module.finrank ℂ (⨅ X : {X : Matrix I I ℂ // X ∈ graph (krausApply E) ∧ X.PosSemidef ∧ X.rank < t},
          kernelSpace X.val : Submodule ℂ (EuclideanSpace ℂ I)) ∧
      Module.finrank ℂ (⨅ X : {X : Matrix I I ℂ // X ∈ graph (krausApply E) ∧ X.PosSemidef ∧ X.rank < t},
          kernelSpace X.val : Submodule ℂ (EuclideanSpace ℂ I)) ≤
        Module.finrank ℂ (⨅ i : {i : Fin r // (E i).rank < t},
          kernelSpace (E i.val) : Submodule ℂ (EuclideanSpace ℂ I)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
