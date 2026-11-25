-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRelevant_comap_map_iff_ce9d308ab38f
-- name    : P2M_GroundTheory_Heights__Heights_isRelevant_comap_map_iff_ce9d308ab38f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:35.286626+00:00
-- url     : https://prove2.me/theorems/f19ce2cd-fbfa-49a1-a41f-f7c4162fd6c0
-- title:
--   P2 M Ground Theory Heights  Heights is Relevant comap map iff ce9d308ab38f: P2 M Ground Theory Heights  Heights is Relevant comap map iff ce9d308ab38f
-- statement:
--   The P2 M Ground Theory Heights  Heights is Relevant comap map iff ce9d308ab38f construction uses the P2 M Ground Theory Heights  Heights is Relevant comap map iff ce9d308ab38f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFundCycleBaseChange.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFundCycleBaseChange.lean#L81-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFundCycleBaseChange
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
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_isRelevant_comap_map_iff_ce9d308ab38f {K L : Type*} [CommRing K] [CommRing L] (σ : K →+* L) {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) L)) :
    IsRelevant (P.comap (MvPolynomial.map σ)) ↔ IsRelevant P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isRelevant_comap_map_iff» := P2M_GroundTheory_Heights__Heights_isRelevant_comap_map_iff_ce9d308ab38f
