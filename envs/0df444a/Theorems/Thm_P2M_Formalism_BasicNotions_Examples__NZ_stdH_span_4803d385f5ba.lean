-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_stdH_span_4803d385f5ba
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_stdH_span_4803d385f5ba
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:11.146072+00:00
-- url     : https://prove2.me/theorems/c8ca0b88-0732-4987-8ebf-804141a0f4a2
-- title:
--   P2 M Formalism Basic Notions Examples  NZ std H span 4803d385f5ba: P2 M Formalism Basic Notions Examples  NZ std H span 4803d385f5ba
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ std H span 4803d385f5ba construction uses the P2 M Formalism Basic Notions Examples  NZ std H span 4803d385f5ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L54-L58

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_stdH_span_4803d385f5ba : Submodule.span K ((stdH K n).L : Set (stdH K n).V) = ⊤ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«stdH_span» := P2M_Formalism_BasicNotions_Examples__NZ_stdH_span_4803d385f5ba
