-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_finOrd_56980a9f4222
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_finOrd_56980a9f4222
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:58.073311+00:00
-- url     : https://prove2.me/theorems/d9994e47-de54-4de7-a8f3-81619fda6e3e
-- title:
--   P2 M Formalism Basic Notions Examples  NZ fin Ord 56980a9f4222: P2 M Formalism Basic Notions Examples  NZ fin Ord 56980a9f4222
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ fin Ord 56980a9f4222 construction uses the P2 M Formalism Basic Notions Examples  NZ fin Ord 56980a9f4222 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L16-L20

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
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

theorem P2M_Formalism_BasicNotions_Examples__NZ_finOrd_56980a9f4222 (i : ℕ) : IsOfFinOrder ((u : Fbar g) ^ (g ^ i)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«finOrd» := P2M_Formalism_BasicNotions_Examples__NZ_finOrd_56980a9f4222
