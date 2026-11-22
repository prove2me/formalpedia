-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_monomial__f1d6e36a6b91
-- name    : P2M_Formalism_MainNotions_PlaneGram_integral_monomial__f1d6e36a6b91
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:51.677039+00:00
-- url     : https://prove2.me/theorems/754888e8-b9ef-471f-ba18-0e7829f28916
-- title:
--   P2 M Formalism Main Notions Plane Gram integral monomial  f1d6e36a6b91: P2 M Formalism Main Notions Plane Gram integral monomial  f1d6e36a6b91
-- statement:
--   The P2 M Formalism Main Notions Plane Gram integral monomial  f1d6e36a6b91 construction uses the P2 M Formalism Main Notions Plane Gram integral monomial  f1d6e36a6b91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L51-L58

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

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
variable {K : Type} [Field K] {v : AddValuation K (WithTop ℚ)} {σ : Type}

theorem P2M_Formalism_MainNotions_PlaneGram_integral_monomial__f1d6e36a6b91 (α : σ →₀ ℕ) {c : K} (hc : 0 ≤ v c) : Integral v (monomial α c) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«integral_monomial'» := P2M_Formalism_MainNotions_PlaneGram_integral_monomial__f1d6e36a6b91
