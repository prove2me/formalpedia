-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_sum_d8cdf6e066f5
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_evS_sum_d8cdf6e066f5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:42.442371+00:00
-- url     : https://prove2.me/theorems/179f7aa9-5a5a-5ade-8517-da827117e9d2
-- title:
--   P2 M Formalism Basic Notions Examples  NZ ev S sum d8cdf6e066f5: P2 M Formalism Basic Notions Examples  NZ ev S sum d8cdf6e066f5
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ ev S sum d8cdf6e066f5 construction uses the P2 M Formalism Basic Notions Examples  NZ ev S sum d8cdf6e066f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L30-L34

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
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
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K]

theorem P2M_Formalism_BasicNotions_Examples__NZ_evS_sum_d8cdf6e066f5 {Γ ι : Type} [Finite Γ] (ψ : Γ → K) (s : Finset ι) (x : ι → MonoidAlgebra K Γ) :
    evS ψ (∑ i ∈ s, x i) = ∑ i ∈ s, evS ψ (x i) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«evS_sum» := P2M_Formalism_BasicNotions_Examples__NZ_evS_sum_d8cdf6e066f5
