-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__mem_primeToSub_e38917aa181c
-- name    : P2M_Formalism_BasicNotions_Examples__mem_primeToSub_e38917aa181c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:33.111544+00:00
-- url     : https://prove2.me/theorems/5dc92238-b8ba-4c99-bd30-ae7a065c735b
-- title:
--   P2 M Formalism Basic Notions Examples  mem prime To Sub e38917aa181c: P2 M Formalism Basic Notions Examples  mem prime To Sub e38917aa181c
-- statement:
--   The P2 M Formalism Basic Notions Examples  mem prime To Sub e38917aa181c construction uses the P2 M Formalism Basic Notions Examples  mem prime To Sub e38917aa181c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/UnitsPowSurjective.lean#L152-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/UnitsPowSurjective.lean#L152-L153

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_UnitsPowSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Cardinal
variable (g l : ℕ) [Fact g.Prime] [Fact l.Prime]
omit [Fact l.Prime]

theorem P2M_Formalism_BasicNotions_Examples__mem_primeToSub_e38917aa181c (x : (AlgebraicClosure (ZMod g))ˣ) :
    x ∈ primeToSub g l ↔ (orderOf x).Coprime l := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«mem_primeToSub» := P2M_Formalism_BasicNotions_Examples__mem_primeToSub_e38917aa181c
