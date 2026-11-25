-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_eT_ne_2dfcaa0d9d00
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_evS_eT_ne_2dfcaa0d9d00
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:41.91334+00:00
-- url     : https://prove2.me/theorems/46b8f2c7-5f25-4c26-823e-5247421d65bc
-- title:
--   P2 M Formalism Basic Notions Examples  NZ ev S e T ne 2dfcaa0d9d00: P2 M Formalism Basic Notions Examples  NZ ev S e T ne 2dfcaa0d9d00
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ ev S e T ne 2dfcaa0d9d00 construction uses the P2 M Formalism Basic Notions Examples  NZ ev S e T ne 2dfcaa0d9d00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L121-L129

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_evS_eT_ne_2dfcaa0d9d00 (ψ : Γ →* K) (g : Γ) (hg : ψ g ≠ 1) : evS ψ (eT K Γ) = 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«evS_eT_ne» := P2M_Formalism_BasicNotions_Examples__NZ_evS_eT_ne_2dfcaa0d9d00
