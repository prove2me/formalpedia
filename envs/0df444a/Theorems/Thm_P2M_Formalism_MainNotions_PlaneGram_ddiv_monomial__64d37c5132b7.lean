-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7
-- name    : P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:09.287592+00:00
-- url     : https://prove2.me/theorems/8f43bbfb-6eca-4fcb-9cf6-c30b5a6cc2db
-- title:
--   P2 M Formalism Main Notions Plane Gram ddiv monomial  64d37c5132b7: P2 M Formalism Main Notions Plane Gram ddiv monomial  64d37c5132b7
-- statement:
--   The P2 M Formalism Main Notions Plane Gram ddiv monomial  64d37c5132b7 construction uses the P2 M Formalism Main Notions Plane Gram ddiv monomial  64d37c5132b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L28-L42

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

theorem P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7 (M α : σ →₀ ℕ) (c : K) :
    ddiv M (monomial α c) = monomial (α - M) (c * bin M α) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«ddiv_monomial'» := P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7
