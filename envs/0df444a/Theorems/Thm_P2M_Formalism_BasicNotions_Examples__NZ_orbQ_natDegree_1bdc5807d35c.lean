-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbQ_natDegree_1bdc5807d35c
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_orbQ_natDegree_1bdc5807d35c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:23.992805+00:00
-- url     : https://prove2.me/theorems/18fed146-3f74-4b5b-bc6c-f0f2a88e5c6a
-- title:
--   P2 M Formalism Basic Notions Examples  NZ orb Q nat Degree 1bdc5807d35c: P2 M Formalism Basic Notions Examples  NZ orb Q nat Degree 1bdc5807d35c
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ orb Q nat Degree 1bdc5807d35c construction uses the P2 M Formalism Basic Notions Examples  NZ orb Q nat Degree 1bdc5807d35c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L92-L94

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_orbQ_natDegree_1bdc5807d35c : (orbQ d u).natDegree = d := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«orbQ_natDegree» := P2M_Formalism_BasicNotions_Examples__NZ_orbQ_natDegree_1bdc5807d35c
