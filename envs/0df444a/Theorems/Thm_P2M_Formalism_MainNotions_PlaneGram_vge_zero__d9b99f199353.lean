-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_zero__d9b99f199353
-- name    : P2M_Formalism_MainNotions_PlaneGram_vge_zero__d9b99f199353
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:08.13508+00:00
-- url     : https://prove2.me/theorems/45ba050d-6858-4df8-90ba-c54b329817a2
-- title:
--   P2 M Formalism Main Notions Plane Gram vge zero  d9b99f199353: P2 M Formalism Main Notions Plane Gram vge zero  d9b99f199353
-- statement:
--   The P2 M Formalism Main Notions Plane Gram vge zero  d9b99f199353 construction uses the P2 M Formalism Main Notions Plane Gram vge zero  d9b99f199353 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L26-L27

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

theorem P2M_Formalism_MainNotions_PlaneGram_vge_zero__d9b99f199353 (a : ℝ) : vge v a (0 : K) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«vge_zero'» := P2M_Formalism_MainNotions_PlaneGram_vge_zero__d9b99f199353
