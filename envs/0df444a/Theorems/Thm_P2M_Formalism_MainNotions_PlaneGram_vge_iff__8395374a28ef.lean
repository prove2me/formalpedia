-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_iff__8395374a28ef
-- name    : P2M_Formalism_MainNotions_PlaneGram_vge_iff__8395374a28ef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:49:58.242441+00:00
-- url     : https://prove2.me/theorems/d5aad393-3d31-43e4-86cb-53fb7f10adab
-- title:
--   P2 M Formalism Main Notions Plane Gram vge iff  8395374a28ef: P2 M Formalism Main Notions Plane Gram vge iff  8395374a28ef
-- statement:
--   The P2 M Formalism Main Notions Plane Gram vge iff  8395374a28ef construction uses the P2 M Formalism Main Notions Plane Gram vge iff  8395374a28ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L16-L24

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

theorem P2M_Formalism_MainNotions_PlaneGram_vge_iff__8395374a28ef (a : ℝ) (x : K) : vge v a x ↔ ∀ n : ℚ, v x = (n : WithTop ℚ) → a ≤ n := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«vge_iff'» := P2M_Formalism_MainNotions_PlaneGram_vge_iff__8395374a28ef
