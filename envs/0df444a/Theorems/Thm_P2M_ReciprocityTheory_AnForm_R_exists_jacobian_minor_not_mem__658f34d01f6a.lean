-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_exists_jacobian_minor_not_mem__658f34d01f6a
-- name    : P2M_ReciprocityTheory_AnForm_R_exists_jacobian_minor_not_mem__658f34d01f6a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:34.464286+00:00
-- url     : https://prove2.me/theorems/86481192-ca68-543e-b269-73699f52f3f6
-- title:
--   P2 M Reciprocity Theory An Form R exists jacobian minor not mem  658f34d01f6a: P2 M Reciprocity Theory An Form R exists jacobian minor not mem  658f34d01f6a
-- statement:
--   The P2 M Reciprocity Theory An Form R exists jacobian minor not mem  658f34d01f6a construction uses the P2 M Reciprocity Theory An Form R exists jacobian minor not mem  658f34d01f6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/GenSmooth.lean#L108-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/GenSmooth.lean#L108-L297

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial

theorem P2M_ReciprocityTheory_AnForm_R_exists_jacobian_minor_not_mem__658f34d01f6a {σ : Type} [Fintype σ]
    (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] {t : ℕ}
    (G : Fin t → MvPolynomial σ ℚ) (hG : Ideal.span (Set.range G) = 𝔭) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) = d) :
    ∃ (a : Fin (Fintype.card σ - d) → Fin t) (b : Fin (Fintype.card σ - d) → σ),
      Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∉ 𝔭 := by sorry

alias «ReciprocityTheory».«AnForm».«R».«exists_jacobian_minor_not_mem'» := P2M_ReciprocityTheory_AnForm_R_exists_jacobian_minor_not_mem__658f34d01f6a
