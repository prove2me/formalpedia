-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_mem_of_local_752b601e4654
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_mem_of_local_752b601e4654
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:51.588978+00:00
-- url     : https://prove2.me/theorems/9b483a86-e9e3-47df-a0b0-4e725cbb0254
-- title:
--   P2 M Formalism Basic Notions Examples  NZ mem of local 752b601e4654: P2 M Formalism Basic Notions Examples  NZ mem of local 752b601e4654
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ mem of local 752b601e4654 construction uses the P2 M Formalism Basic Notions Examples  NZ mem of local 752b601e4654 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L199-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L199-L218

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
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
open NumberField IsDedekindDomain Formalism.BasicNotions

theorem P2M_Formalism_BasicNotions_Examples__NZ_mem_of_local_752b601e4654 {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (Λ : Submodule A M) (x : M)
    (h : ∀ P : Ideal A, P.IsMaximal → ∃ d : A, d ∉ P ∧ d • x ∈ Λ) : x ∈ Λ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«mem_of_local» := P2M_Formalism_BasicNotions_Examples__NZ_mem_of_local_752b601e4654
