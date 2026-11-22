-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_mono__13f616ce561b
-- name    : P2M_Formalism_MainNotions_PlaneGram_vge_mono__13f616ce561b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:27:14.22948+00:00
-- url     : https://prove2.me/theorems/1be1f726-3ae2-4c0d-87da-4791f58abde0
-- title:
--   P2 M Formalism Main Notions Plane Gram vge mono  13f616ce561b: P2 M Formalism Main Notions Plane Gram vge mono  13f616ce561b
-- statement:
--   The P2 M Formalism Main Notions Plane Gram vge mono  13f616ce561b construction uses the P2 M Formalism Main Notions Plane Gram vge mono  13f616ce561b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L29-L30

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

theorem P2M_Formalism_MainNotions_PlaneGram_vge_mono__13f616ce561b {a b : ℝ} {x : K} (hab : b ≤ a) (h : vge v a x) : vge v b x := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«vge_mono'» := P2M_Formalism_MainNotions_PlaneGram_vge_mono__13f616ce561b
