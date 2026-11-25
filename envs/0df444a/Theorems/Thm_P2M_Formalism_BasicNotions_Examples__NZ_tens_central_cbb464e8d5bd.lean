-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_central_cbb464e8d5bd
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_tens_central_cbb464e8d5bd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:08.517535+00:00
-- url     : https://prove2.me/theorems/39fecc98-f297-4cd0-9d4d-c5d530d01e09
-- title:
--   P2 M Formalism Basic Notions Examples  NZ tens central cbb464e8d5bd: P2 M Formalism Basic Notions Examples  NZ tens central cbb464e8d5bd
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ tens central cbb464e8d5bd construction uses the P2 M Formalism Basic Notions Examples  NZ tens central cbb464e8d5bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L69-L74

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_tens_central_cbb464e8d5bd (x : ∀ i, MonoidAlgebra k (G i)) (h : ∀ i a, x i * a = a * x i)
    (a : MonoidAlgebra k (∀ i, G i)) : tens x * a = a * tens x := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«tens_central» := P2M_Formalism_BasicNotions_Examples__NZ_tens_central_cbb464e8d5bd
