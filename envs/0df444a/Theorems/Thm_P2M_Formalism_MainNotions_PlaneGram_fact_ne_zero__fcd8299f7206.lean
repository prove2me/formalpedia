-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_fact_ne_zero__fcd8299f7206
-- name    : P2M_Formalism_MainNotions_PlaneGram_fact_ne_zero__fcd8299f7206
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:05:11.548011+00:00
-- url     : https://prove2.me/theorems/8cdd323b-17ba-45a9-a9b4-dbe5ce65081e
-- title:
--   P2 M Formalism Main Notions Plane Gram fact ne zero  fcd8299f7206: P2 M Formalism Main Notions Plane Gram fact ne zero  fcd8299f7206
-- statement:
--   The P2 M Formalism Main Notions Plane Gram fact ne zero  fcd8299f7206 construction uses the P2 M Formalism Main Notions Plane Gram fact ne zero  fcd8299f7206 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L62-L64

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

theorem P2M_Formalism_MainNotions_PlaneGram_fact_ne_zero__fcd8299f7206 {σ : Type} (α : σ →₀ ℕ) : fact α ≠ 0 := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«fact_ne_zero'» := P2M_Formalism_MainNotions_PlaneGram_fact_ne_zero__fcd8299f7206
