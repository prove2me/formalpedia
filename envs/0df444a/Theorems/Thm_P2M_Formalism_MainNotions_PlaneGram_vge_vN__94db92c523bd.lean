-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_vN__94db92c523bd
-- name    : P2M_Formalism_MainNotions_PlaneGram_vge_vN__94db92c523bd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:00.463462+00:00
-- url     : https://prove2.me/theorems/f02b92b2-58bf-4c57-bb88-217465320737
-- title:
--   P2 M Formalism Main Notions Plane Gram vge v N  94db92c523bd: P2 M Formalism Main Notions Plane Gram vge v N  94db92c523bd
-- statement:
--   The P2 M Formalism Main Notions Plane Gram vge v N  94db92c523bd construction uses the P2 M Formalism Main Notions Plane Gram vge v N  94db92c523bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L66-L70

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

theorem P2M_Formalism_MainNotions_PlaneGram_vge_vN__94db92c523bd (n : ℕ) : vge v (vN v n) (n : K) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«vge_vN'» := P2M_Formalism_MainNotions_PlaneGram_vge_vN__94db92c523bd
