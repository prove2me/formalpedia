-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_lg_mono__9d5245f1fc9a
-- name    : P2M_Formalism_MainNotions_PlaneGram_lg_mono__9d5245f1fc9a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:55.017607+00:00
-- url     : https://prove2.me/theorems/77cadb30-e100-4868-929f-fc026c30a967
-- title:
--   P2 M Formalism Main Notions Plane Gram lg mono  9d5245f1fc9a: P2 M Formalism Main Notions Plane Gram lg mono  9d5245f1fc9a
-- statement:
--   The P2 M Formalism Main Notions Plane Gram lg mono  9d5245f1fc9a construction uses the P2 M Formalism Main Notions Plane Gram lg mono  9d5245f1fc9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L17-L27

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

theorem P2M_Formalism_MainNotions_PlaneGram_lg_mono__9d5245f1fc9a {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) {a b : ℕ} (hab : a ≤ b) :
    lg p r a ≤ lg p r b := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«lg_mono'» := P2M_Formalism_MainNotions_PlaneGram_lg_mono__9d5245f1fc9a
