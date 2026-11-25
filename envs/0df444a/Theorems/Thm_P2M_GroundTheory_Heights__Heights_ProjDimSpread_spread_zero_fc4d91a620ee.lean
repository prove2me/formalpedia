-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_zero_fc4d91a620ee
-- name    : P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_zero_fc4d91a620ee
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:31.908656+00:00
-- url     : https://prove2.me/theorems/27b3f806-99bd-4d3b-bc60-81db69c55153
-- title:
--   P2 M Ground Theory Heights  Heights Proj Dim Spread spread zero fc4d91a620ee: P2 M Ground Theory Heights  Heights Proj Dim Spread spread zero fc4d91a620ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Dim Spread spread zero fc4d91a620ee construction uses the P2 M Ground Theory Heights  Heights Proj Dim Spread spread zero fc4d91a620ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjDimSpread.lean#L25-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjDimSpread.lean#L25-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjDimSpread
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjDimSpread
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open CategoryTheory
variable {R : Type} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_zero_fc4d91a620ee [IsNoetherianRing R] (P : Ideal R) [P.IsPrime]
    (M : ModuleCat.{0} R) [Module.Finite R M]
    (h : HasProjectiveDimensionLE (M.localizedModule P.primeCompl) 0) :
    ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
      HasProjectiveDimensionLE (M.localizedModule Q.primeCompl) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjDimSpread».«spread_zero» := P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_zero_fc4d91a620ee
