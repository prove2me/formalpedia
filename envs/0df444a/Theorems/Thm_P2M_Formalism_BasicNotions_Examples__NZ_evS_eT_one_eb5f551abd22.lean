-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_eT_one_eb5f551abd22
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_evS_eT_one_eb5f551abd22
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:03.699708+00:00
-- url     : https://prove2.me/theorems/8dec24a1-61a7-556b-8860-aad03278c02f
-- title:
--   P2 M Formalism Basic Notions Examples  NZ ev S e T one eb5f551abd22: P2 M Formalism Basic Notions Examples  NZ ev S e T one eb5f551abd22
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ ev S e T one eb5f551abd22 construction uses the P2 M Formalism Basic Notions Examples  NZ ev S e T one eb5f551abd22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L115-L119

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
variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]
variable {K Γ}

theorem P2M_Formalism_BasicNotions_Examples__NZ_evS_eT_one_eb5f551abd22 [CharZero K] : evS (fun _ : Γ => (1 : K)) (eT K Γ) = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«evS_eT_one» := P2M_Formalism_BasicNotions_Examples__NZ_evS_eT_one_eb5f551abd22
