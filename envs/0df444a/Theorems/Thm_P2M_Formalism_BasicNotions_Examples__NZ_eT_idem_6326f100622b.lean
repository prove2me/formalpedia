-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eT_idem_6326f100622b
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_eT_idem_6326f100622b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:06.473715+00:00
-- url     : https://prove2.me/theorems/7564c8d4-ce26-47f3-ab6e-cb10e4acd0fd
-- title:
--   P2 M Formalism Basic Notions Examples  NZ e T idem 6326f100622b: P2 M Formalism Basic Notions Examples  NZ e T idem 6326f100622b
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ e T idem 6326f100622b construction uses the P2 M Formalism Basic Notions Examples  NZ e T idem 6326f100622b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L92-L98

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_eT_idem_6326f100622b [CharZero K] : eT K Γ * eT K Γ = eT K Γ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«eT_idem» := P2M_Formalism_BasicNotions_Examples__NZ_eT_idem_6326f100622b
