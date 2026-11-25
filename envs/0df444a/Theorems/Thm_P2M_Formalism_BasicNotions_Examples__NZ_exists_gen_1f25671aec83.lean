-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_1f25671aec83
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_1f25671aec83
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:51.317805+00:00
-- url     : https://prove2.me/theorems/8b011e9f-bee0-4572-8cc6-066e24a2b4d5
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exists gen 1f25671aec83: P2 M Formalism Basic Notions Examples  NZ exists gen 1f25671aec83
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exists gen 1f25671aec83 construction uses the P2 M Formalism Basic Notions Examples  NZ exists gen 1f25671aec83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L26-L38

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_1f25671aec83 (d : ℕ) (hd : 1 ≤ d) : ∃ u : (Fbar g)ˣ, orderOf u = g ^ d - 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exists_gen» := P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_1f25671aec83
