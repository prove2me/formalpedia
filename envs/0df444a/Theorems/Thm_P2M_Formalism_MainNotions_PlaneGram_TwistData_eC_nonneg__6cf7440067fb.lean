-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_TwistData_eC_nonneg__6cf7440067fb
-- name    : P2M_Formalism_MainNotions_PlaneGram_TwistData_eC_nonneg__6cf7440067fb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:36.897807+00:00
-- url     : https://prove2.me/theorems/8714f0fe-249d-4143-b5ad-35e1854c7650
-- title:
--   P2 M Formalism Main Notions Plane Gram Twist Data e C nonneg  6cf7440067fb: P2 M Formalism Main Notions Plane Gram Twist Data e C nonneg  6cf7440067fb
-- statement:
--   The P2 M Formalism Main Notions Plane Gram Twist Data e C nonneg  6cf7440067fb construction uses the P2 M Formalism Main Notions Plane Gram Twist Data e C nonneg  6cf7440067fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CardLinkIdxMulLe.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CardLinkIdxMulLe.lean#L86-L89

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)

theorem P2M_Formalism_MainNotions_PlaneGram_TwistData_eC_nonneg__6cf7440067fb {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.eC p C0 := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«TwistData».«eC_nonneg'» := P2M_Formalism_MainNotions_PlaneGram_TwistData_eC_nonneg__6cf7440067fb
