-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma9_1_one_eigenline
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma9_1_one_eigenline
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:48:22.22926+00:00
-- url     : https://prove2.me/theorems/eaaa825e-d8f2-49f3-bcad-62d92dc41f8c
-- title:
--   Lemma 9.1: each Jordan block has one eigenline
-- statement:
--   Let $\mathcal E$ be a complex-linear endomorphism of a finite-dimensional nonzero operator space. Choose a positive-length Jordan chain $v_0,\ldots,v_{m-1}$ for eigenvalue $z$, with the similarity to physical coordinates already applied. In its span, the nonzero eigenvectors are exactly
--
--   $$\mathcal E(X)=wX\iff w=z\ \text{ and }\ X=cv_0\text{ for some }c\ne0.$$
--
--   Also $\mathcal E(v_0)=zv_0$. The printed “exactly one unit eigenvector” is corrected to one eigenline, as required by the source proof: phases give distinct unit eigenvectors. No CP, TP or orthogonality assumption is needed.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 27, Lemma 9.1: each Jordan block has one eigenline

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.27, Lemma 9.1, corrected as its proof requires: the printed 'exactly
one unit eigenvector' is changed to one eigenline, because v and -v are distinct
unit eigenvectors. The Jordan chain is transported through S; no orthogonality
of different eigenlines is asserted. Independent moderation of this correction is pending. -/
theorem lemma9_1_one_eigenline {I : Type*} [Fintype I] [Nonempty I]
    {m : ℕ} (hm : 0 < m)
    (E : Op I →ₗ[ℂ] Op I) (z : ℂ) (v : Fin m → Op I) (hv : IsJordanChain E z v) :
    E (v ⟨0, hm⟩) = z • v ⟨0, hm⟩ ∧
    ∀ X ∈ Submodule.span ℂ (Set.range v), ∀ w : ℂ, X ≠ 0 →
      (E X = w • X ↔ w = z ∧ ∃ c : ℂ, c ≠ 0 ∧ X = c • v ⟨0, hm⟩) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
