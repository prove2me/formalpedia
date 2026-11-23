-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_sum__98181df79b27
-- name    : P2M_Formalism_MainNotions_PlaneGram_vge_sum__98181df79b27
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:07.418424+00:00
-- url     : https://prove2.me/theorems/2e0fa63d-5f2a-4d2d-b678-cbb39c983887
-- title:
--   P2 M Formalism Main Notions Plane Gram vge sum  98181df79b27: P2 M Formalism Main Notions Plane Gram vge sum  98181df79b27
-- statement:
--   The P2 M Formalism Main Notions Plane Gram vge sum  98181df79b27 construction uses the P2 M Formalism Main Notions Plane Gram vge sum  98181df79b27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L58-L60

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

theorem P2M_Formalism_MainNotions_PlaneGram_vge_sum__98181df79b27 {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, vge v a (f i)) :
    vge v a (∑ i ∈ s, f i) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«vge_sum'» := P2M_Formalism_MainNotions_PlaneGram_vge_sum__98181df79b27
