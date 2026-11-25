-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbit_inj_7a2eb0016b77
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_orbit_inj_7a2eb0016b77
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:04.830286+00:00
-- url     : https://prove2.me/theorems/b1af74d1-6848-46f8-9d0d-29843973d1b6
-- title:
--   P2 M Formalism Basic Notions Examples  NZ orbit inj 7a2eb0016b77: P2 M Formalism Basic Notions Examples  NZ orbit inj 7a2eb0016b77
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ orbit inj 7a2eb0016b77 construction uses the P2 M Formalism Basic Notions Examples  NZ orbit inj 7a2eb0016b77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L69-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L69-L86

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_orbit_inj_7a2eb0016b77 {i j : ℕ} (hi : i < d) (hj : j < d) (h : u ^ (g ^ i) = u ^ (g ^ j)) : i = j := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«orbit_inj» := P2M_Formalism_BasicNotions_Examples__NZ_orbit_inj_7a2eb0016b77
