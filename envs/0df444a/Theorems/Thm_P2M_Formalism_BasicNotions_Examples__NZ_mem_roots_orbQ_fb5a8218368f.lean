-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_mem_roots_orbQ_fb5a8218368f
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_mem_roots_orbQ_fb5a8218368f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:13.155485+00:00
-- url     : https://prove2.me/theorems/6657ddc8-10f7-4f88-ae8f-652708c2f0c9
-- title:
--   P2 M Formalism Basic Notions Examples  NZ mem roots orb Q fb5a8218368f: P2 M Formalism Basic Notions Examples  NZ mem roots orb Q fb5a8218368f
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ mem roots orb Q fb5a8218368f construction uses the P2 M Formalism Basic Notions Examples  NZ mem roots orb Q fb5a8218368f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L144-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L144-L148

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_mem_roots_orbQ_fb5a8218368f {y : Fbar g} : y ∈ (orbQ d u).roots ↔ ∃ i < d, y = (u : Fbar g) ^ (g ^ i) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«mem_roots_orbQ» := P2M_Formalism_BasicNotions_Examples__NZ_mem_roots_orbQ_fb5a8218368f
