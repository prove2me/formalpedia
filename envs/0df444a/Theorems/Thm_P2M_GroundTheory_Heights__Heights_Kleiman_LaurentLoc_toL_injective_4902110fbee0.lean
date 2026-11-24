-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_injective_4902110fbee0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_injective_4902110fbee0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:51.568906+00:00
-- url     : https://prove2.me/theorems/f6f08312-9acb-4840-8e87-b58f76a71196
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc to L injective 4902110fbee0: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc to L injective 4902110fbee0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc to L injective 4902110fbee0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc to L injective 4902110fbee0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L34-L36

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_injective_4902110fbee0 : Function.Injective (toL S N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«toL_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_injective_4902110fbee0
