-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vala_iff_Aset__0ad87ad3abdb
-- name    : P2M_Formalism_MainNotions_PlaneGram_vala_iff_Aset__0ad87ad3abdb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:05:06.375208+00:00
-- url     : https://prove2.me/theorems/6b9f5de6-664c-5e00-91cc-e5289b0e2a78
-- title:
--   P2 M Formalism Main Notions Plane Gram vala iff Aset  0ad87ad3abdb: P2 M Formalism Main Notions Plane Gram vala iff Aset  0ad87ad3abdb
-- statement:
--   The P2 M Formalism Main Notions Plane Gram vala iff Aset  0ad87ad3abdb construction uses the P2 M Formalism Main Notions Plane Gram vala iff Aset  0ad87ad3abdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L13-L15

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

theorem P2M_Formalism_MainNotions_PlaneGram_vala_iff_Aset__0ad87ad3abdb {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (θ : ℝ)
    (F : MvPolynomial (L × Fin r) K) : vala sg S θ F ↔ F ∈ Aset sg S ⌈θ⌉ := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«vala_iff_Aset'» := P2M_Formalism_MainNotions_PlaneGram_vala_iff_Aset__0ad87ad3abdb
