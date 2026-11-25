-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_esZ_one_cfadaa65a069
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_evS_esZ_one_cfadaa65a069
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:51.907037+00:00
-- url     : https://prove2.me/theorems/5197c9ff-fc90-438d-a8c2-9ecc5f2fcfc9
-- title:
--   P2 M Formalism Basic Notions Examples  NZ ev S es Z one cfadaa65a069: P2 M Formalism Basic Notions Examples  NZ ev S es Z one cfadaa65a069
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ ev S es Z one cfadaa65a069 construction uses the P2 M Formalism Basic Notions Examples  NZ ev S es Z one cfadaa65a069 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L187-L194

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
variable (K : Type) [Field K] (Γ : Type) {Λ : Type} [Group Γ] [Finite Γ] (fA fB : Λ)
variable {K Γ fA fB} [CharZero K] (hAB : fA ≠ fB)
include hAB

theorem P2M_Formalism_BasicNotions_Examples__NZ_evS_esZ_one_cfadaa65a069 (f : Λ) : evS (fun _ : Γ => (1 : K)) (esZ K Γ fA fB f) = if f = fB then 1 else 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«evS_esZ_one» := P2M_Formalism_BasicNotions_Examples__NZ_evS_esZ_one_cfadaa65a069
