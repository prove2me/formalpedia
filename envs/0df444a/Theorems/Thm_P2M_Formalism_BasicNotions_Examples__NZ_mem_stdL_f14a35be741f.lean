-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_mem_stdL_f14a35be741f
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_mem_stdL_f14a35be741f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:15.296335+00:00
-- url     : https://prove2.me/theorems/6fff9bf5-e98b-44df-832b-2935a6c2aa1b
-- title:
--   P2 M Formalism Basic Notions Examples  NZ mem std L f14a35be741f: P2 M Formalism Basic Notions Examples  NZ mem std L f14a35be741f
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ mem std L f14a35be741f construction uses the P2 M Formalism Basic Notions Examples  NZ mem std L f14a35be741f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L21-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L21-L52

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
variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)

theorem P2M_Formalism_BasicNotions_Examples__NZ_mem_stdL_f14a35be741f (x : Fin n → K) : x ∈ (stdH K n).L ↔ ∀ i, ∃ c : 𝓞 K, x i = (c : K) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«mem_stdL» := P2M_Formalism_BasicNotions_Examples__NZ_mem_stdL_f14a35be741f
