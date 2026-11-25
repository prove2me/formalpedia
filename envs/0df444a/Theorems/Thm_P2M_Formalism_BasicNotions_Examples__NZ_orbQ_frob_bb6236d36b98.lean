-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbQ_frob_bb6236d36b98
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_orbQ_frob_bb6236d36b98
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:32.453068+00:00
-- url     : https://prove2.me/theorems/75affc96-27cd-42fa-acb1-5d8d0ec7cfb6
-- title:
--   P2 M Formalism Basic Notions Examples  NZ orb Q frob bb6236d36b98: P2 M Formalism Basic Notions Examples  NZ orb Q frob bb6236d36b98
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ orb Q frob bb6236d36b98 construction uses the P2 M Formalism Basic Notions Examples  NZ orb Q frob bb6236d36b98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L97-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L97-L109

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
include hd hu

theorem P2M_Formalism_BasicNotions_Examples__NZ_orbQ_frob_bb6236d36b98 : (orbQ d u).map (frobenius (Fbar g) g) = orbQ d u := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«orbQ_frob» := P2M_Formalism_BasicNotions_Examples__NZ_orbQ_frob_bb6236d36b98
