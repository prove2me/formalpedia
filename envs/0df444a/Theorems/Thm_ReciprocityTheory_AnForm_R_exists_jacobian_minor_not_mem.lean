-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_jacobian_minor_not_mem
-- name    : ReciprocityTheory.AnForm.R.exists_jacobian_minor_not_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:44.637145+00:00
-- url     : https://prove2.me/theorems/c64faebd-ea31-47d6-8a2e-96ff8393a6dd
-- title:
--   R: exists jacobian minor not mem
-- statement:
--   The R construction uses the exists jacobian minor not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/GenSmooth.lean#L299-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/GenSmooth.lean#L299-L305

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

theorem ReciprocityTheory.AnForm.R.exists_jacobian_minor_not_mem {σ : Type} [Fintype σ]
    (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] {t : ℕ}
    (G : Fin t → MvPolynomial σ ℚ) (hG : Ideal.span (Set.range G) = 𝔭) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) = d) :
    ∃ (a : Fin (Fintype.card σ - d) → Fin t) (b : Fin (Fintype.card σ - d) → σ),
      Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∉ 𝔭 := by sorry
