-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_injective_5250b9913735
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_injective_5250b9913735
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:11.462818+00:00
-- url     : https://prove2.me/theorems/6d7b6f55-9a70-544c-ab4e-20ee4913c3e0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota injective 5250b9913735: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota injective 5250b9913735
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota injective 5250b9913735 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota injective 5250b9913735 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L193-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L193-L194

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
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_injective_5250b9913735 (I : StdCell N) : Function.Injective (iota (S := S) I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«iota_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_injective_5250b9913735
