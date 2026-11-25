-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_one_8cef7cfb33bc
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_evS_one_8cef7cfb33bc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:32:54.3359+00:00
-- url     : https://prove2.me/theorems/a697efd9-76dc-5b85-b8c3-771d076c0869
-- title:
--   P2 M Formalism Basic Notions Examples  NZ ev S one 8cef7cfb33bc: P2 M Formalism Basic Notions Examples  NZ ev S one 8cef7cfb33bc
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ ev S one 8cef7cfb33bc construction uses the P2 M Formalism Basic Notions Examples  NZ ev S one 8cef7cfb33bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L36-L42

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_evS_one_8cef7cfb33bc {Γ : Type} [Group Γ] [Finite Γ] (ψ : Γ → K) : evS ψ (1 : MonoidAlgebra K Γ) = ψ 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«evS_one» := P2M_Formalism_BasicNotions_Examples__NZ_evS_one_8cef7cfb33bc
