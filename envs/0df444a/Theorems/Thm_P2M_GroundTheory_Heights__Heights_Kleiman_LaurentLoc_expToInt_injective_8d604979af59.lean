-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_expToInt_injective_8d604979af59
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_expToInt_injective_8d604979af59
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:19.195748+00:00
-- url     : https://prove2.me/theorems/93c6ff8d-a634-4292-92e9-b16302d9a10e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc exp To Int injective 8d604979af59: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc exp To Int injective 8d604979af59
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc exp To Int injective 8d604979af59 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc exp To Int injective 8d604979af59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L23-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable (S : Type u) [CommRing S] (N : ℕ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_expToInt_injective_8d604979af59 : Function.Injective (expToInt N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«expToInt_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_expToInt_injective_8d604979af59
