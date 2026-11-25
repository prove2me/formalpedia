-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_lg_nonneg__7f797abb6a20
-- name    : P2M_Formalism_MainNotions_PlaneGram_lg_nonneg__7f797abb6a20
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:03.858495+00:00
-- url     : https://prove2.me/theorems/17e967c8-e219-4dcc-997e-a962cb292b37
-- title:
--   P2 M Formalism Main Notions Plane Gram lg nonneg  7f797abb6a20: P2 M Formalism Main Notions Plane Gram lg nonneg  7f797abb6a20
-- statement:
--   The P2 M Formalism Main Notions Plane Gram lg nonneg  7f797abb6a20 construction uses the P2 M Formalism Main Notions Plane Gram lg nonneg  7f797abb6a20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L29-L36

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
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

theorem P2M_Formalism_MainNotions_PlaneGram_lg_nonneg__7f797abb6a20 {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) (a : ℕ) : 0 ≤ lg p r a := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«lg_nonneg'» := P2M_Formalism_MainNotions_PlaneGram_lg_nonneg__7f797abb6a20
