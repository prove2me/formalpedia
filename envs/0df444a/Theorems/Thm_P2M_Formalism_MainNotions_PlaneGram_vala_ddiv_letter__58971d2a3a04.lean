-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vala_ddiv_letter__58971d2a3a04
-- name    : P2M_Formalism_MainNotions_PlaneGram_vala_ddiv_letter__58971d2a3a04
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:11.142799+00:00
-- url     : https://prove2.me/theorems/51b979e4-74d6-4c4e-831e-138d2bec1da7
-- title:
--   P2 M Formalism Main Notions Plane Gram vala ddiv letter  58971d2a3a04: P2 M Formalism Main Notions Plane Gram vala ddiv letter  58971d2a3a04
-- statement:
--   The P2 M Formalism Main Notions Plane Gram vala ddiv letter  58971d2a3a04 construction uses the P2 M Formalism Main Notions Plane Gram vala ddiv letter  58971d2a3a04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1057-L1063
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1057-L1063

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
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
variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}

theorem P2M_Formalism_MainNotions_PlaneGram_vala_ddiv_letter__58971d2a3a04 (hV2 : V2 K) {θ : ℝ} (i : L) (β : Fin r →₀ ℕ)
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S (θ - (if sg i then (absE β : ℝ) else 0)) (ddiv (onLetter i β) F) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«vala_ddiv_letter'» := P2M_Formalism_MainNotions_PlaneGram_vala_ddiv_letter__58971d2a3a04
