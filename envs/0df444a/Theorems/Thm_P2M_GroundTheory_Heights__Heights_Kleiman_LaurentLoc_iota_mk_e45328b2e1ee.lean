-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_mk_e45328b2e1ee
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_mk_e45328b2e1ee
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:18.596724+00:00
-- url     : https://prove2.me/theorems/128c29d8-0e12-569f-9fdb-0070c560978d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota mk e45328b2e1ee: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota mk e45328b2e1ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota mk e45328b2e1ee construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota mk e45328b2e1ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L174-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L174-L181

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_mk_e45328b2e1ee (I : StdCell N) (p : Poly S N) :
    iota I (locMk (Poly S N) I.1 p) = polyToLaurent S N p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«iota_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_mk_e45328b2e1ee
