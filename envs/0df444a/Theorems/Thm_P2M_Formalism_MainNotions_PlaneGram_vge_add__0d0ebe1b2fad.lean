-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_add__0d0ebe1b2fad
-- name    : P2M_Formalism_MainNotions_PlaneGram_vge_add__0d0ebe1b2fad
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:06.538065+00:00
-- url     : https://prove2.me/theorems/b34f4cda-8d84-426e-b5bb-46c769489168
-- title:
--   P2 M Formalism Main Notions Plane Gram vge add  0d0ebe1b2fad: P2 M Formalism Main Notions Plane Gram vge add  0d0ebe1b2fad
-- statement:
--   The P2 M Formalism Main Notions Plane Gram vge add  0d0ebe1b2fad construction uses the P2 M Formalism Main Notions Plane Gram vge add  0d0ebe1b2fad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L32-L41

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
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
variable (v : AddValuation K (WithTop ℚ))

theorem P2M_Formalism_MainNotions_PlaneGram_vge_add__0d0ebe1b2fad {a : ℝ} {x y : K} (hx : vge v a x) (hy : vge v a y) : vge v a (x + y) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«vge_add'» := P2M_Formalism_MainNotions_PlaneGram_vge_add__0d0ebe1b2fad
