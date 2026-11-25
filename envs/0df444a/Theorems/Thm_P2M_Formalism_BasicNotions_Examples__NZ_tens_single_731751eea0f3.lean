-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_single_731751eea0f3
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_tens_single_731751eea0f3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:04.925887+00:00
-- url     : https://prove2.me/theorems/8200d7d5-5683-441a-be21-50a0eae591df
-- title:
--   P2 M Formalism Basic Notions Examples  NZ tens single 731751eea0f3: P2 M Formalism Basic Notions Examples  NZ tens single 731751eea0f3
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ tens single 731751eea0f3 construction uses the P2 M Formalism Basic Notions Examples  NZ tens single 731751eea0f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L48-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L48-L58

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
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
open MonoidAlgebra
variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem P2M_Formalism_BasicNotions_Examples__NZ_tens_single_731751eea0f3 [DecidableEq I] (g : ∀ i, G i) : tens (fun i => (single (g i) 1 : MonoidAlgebra k (G i))) = single g 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«tens_single» := P2M_Formalism_BasicNotions_Examples__NZ_tens_single_731751eea0f3
