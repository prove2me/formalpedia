-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_expand_monomial__8cd8bb5d66fe
-- name    : P2M_Formalism_MainNotions_PlaneGram_expand_monomial__8cd8bb5d66fe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:21.41382+00:00
-- url     : https://prove2.me/theorems/c86d2730-1cde-4701-9460-c2cf50562820
-- title:
--   P2 M Formalism Main Notions Plane Gram expand monomial  8cd8bb5d66fe: P2 M Formalism Main Notions Plane Gram expand monomial  8cd8bb5d66fe
-- statement:
--   The P2 M Formalism Main Notions Plane Gram expand monomial  8cd8bb5d66fe construction uses the P2 M Formalism Main Notions Plane Gram expand monomial  8cd8bb5d66fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L70-L74

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {K : Type} [Field K]
variable {σ : Type} [Fintype σ]

theorem P2M_Formalism_MainNotions_PlaneGram_expand_monomial__8cd8bb5d66fe {τ : Type} (P : ℕ) (d : τ →₀ ℕ) (c : K) :
    expand P (monomial d c) = monomial (P • d) c := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«expand_monomial'» := P2M_Formalism_MainNotions_PlaneGram_expand_monomial__8cd8bb5d66fe
