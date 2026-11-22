-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_mul__293e99e62721
-- name    : P2M_Formalism_MainNotions_PlaneGram_vge_mul__293e99e62721
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:45.977354+00:00
-- url     : https://prove2.me/theorems/48e01340-6b39-4fe1-b235-dd498f3821e5
-- title:
--   P2 M Formalism Main Notions Plane Gram vge mul  293e99e62721: P2 M Formalism Main Notions Plane Gram vge mul  293e99e62721
-- statement:
--   The P2 M Formalism Main Notions Plane Gram vge mul  293e99e62721 construction uses the P2 M Formalism Main Notions Plane Gram vge mul  293e99e62721 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L43-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L43-L56

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

theorem P2M_Formalism_MainNotions_PlaneGram_vge_mul__293e99e62721 {a b : ℝ} {x y : K} (hx : vge v a x) (hy : vge v b y) : vge v (a + b) (x * y) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«vge_mul'» := P2M_Formalism_MainNotions_PlaneGram_vge_mul__293e99e62721
