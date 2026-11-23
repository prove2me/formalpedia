-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_mul_c3492ccc8731
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_tens_mul_c3492ccc8731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:54.141784+00:00
-- url     : https://prove2.me/theorems/dc632dc7-5480-46df-bb39-5c7e8e12bafc
-- title:
--   P2 M Formalism Basic Notions Examples  NZ tens mul c3492ccc8731: P2 M Formalism Basic Notions Examples  NZ tens mul c3492ccc8731
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ tens mul c3492ccc8731 construction uses the P2 M Formalism Basic Notions Examples  NZ tens mul c3492ccc8731 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L21-L29

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_tens_mul_c3492ccc8731 (x y : ∀ i, MonoidAlgebra k (G i)) : tens x * tens y = tens fun i => x i * y i := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«tens_mul» := P2M_Formalism_BasicNotions_Examples__NZ_tens_mul_c3492ccc8731
