-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_8b8fc0279bd0
-- name    : P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_8b8fc0279bd0
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:16.540818+00:00
-- url     : https://prove2.me/theorems/dc4b2369-3773-49a2-b81b-491de030bf3e
-- title:
--   P2 M Ground Theory Heights  Heights Proj Dim Spread spread 8b8fc0279bd0: P2 M Ground Theory Heights  Heights Proj Dim Spread spread 8b8fc0279bd0
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Dim Spread spread 8b8fc0279bd0 construction uses the P2 M Ground Theory Heights  Heights Proj Dim Spread spread 8b8fc0279bd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjDimSpread.lean#L46-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjDimSpread.lean#L46-L68

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

theorem P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_8b8fc0279bd0 [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (n : ℕ) :
    ∀ (M : ModuleCat.{0} R) [Module.Finite R M],
      HasProjectiveDimensionLE (M.localizedModule P.primeCompl) n →
      ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
        HasProjectiveDimensionLE (M.localizedModule Q.primeCompl) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjDimSpread».«spread» := P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_8b8fc0279bd0
