-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_ne_zero_47cbf78b02c5
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_tens_ne_zero_47cbf78b02c5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:09.954217+00:00
-- url     : https://prove2.me/theorems/92d7d723-33ad-40f1-b369-baffd7c48189
-- title:
--   P2 M Formalism Basic Notions Examples  NZ tens ne zero 47cbf78b02c5: P2 M Formalism Basic Notions Examples  NZ tens ne zero 47cbf78b02c5
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ tens ne zero 47cbf78b02c5 construction uses the P2 M Formalism Basic Notions Examples  NZ tens ne zero 47cbf78b02c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L37-L46

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_tens_ne_zero_47cbf78b02c5 (x : ∀ i, MonoidAlgebra k (G i)) (h : ∀ i, x i ≠ 0) : tens x ≠ 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«tens_ne_zero» := P2M_Formalism_BasicNotions_Examples__NZ_tens_ne_zero_47cbf78b02c5
