-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_eq_zero_39ca149e5dc3
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_tens_eq_zero_39ca149e5dc3
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:59.512953+00:00
-- url     : https://prove2.me/theorems/13e519fd-f98a-4df9-8a1a-d3ea7368f9f9
-- title:
--   P2 M Formalism Basic Notions Examples  NZ tens eq zero 39ca149e5dc3: P2 M Formalism Basic Notions Examples  NZ tens eq zero 39ca149e5dc3
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ tens eq zero 39ca149e5dc3 construction uses the P2 M Formalism Basic Notions Examples  NZ tens eq zero 39ca149e5dc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L31-L35

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_tens_eq_zero_39ca149e5dc3 (x : ∀ i, MonoidAlgebra k (G i)) (i : I) (h : x i = 0) : tens x = 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«tens_eq_zero» := P2M_Formalism_BasicNotions_Examples__NZ_tens_eq_zero_39ca149e5dc3
