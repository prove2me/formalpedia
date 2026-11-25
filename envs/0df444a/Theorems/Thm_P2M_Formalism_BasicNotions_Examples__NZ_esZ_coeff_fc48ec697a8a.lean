-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_esZ_coeff_fc48ec697a8a
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_esZ_coeff_fc48ec697a8a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:44.232949+00:00
-- url     : https://prove2.me/theorems/8ba18abb-28e4-46db-bf49-901c37041e2e
-- title:
--   P2 M Formalism Basic Notions Examples  NZ es Z coeff fc48ec697a8a: P2 M Formalism Basic Notions Examples  NZ es Z coeff fc48ec697a8a
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ es Z coeff fc48ec697a8a construction uses the P2 M Formalism Basic Notions Examples  NZ es Z coeff fc48ec697a8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L143-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L143-L145

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_esZ_coeff_fc48ec697a8a [CharZero K] (f : Λ) (h : Γ) : (esZ K Γ fA fB f).coeff h = (cfQ Γ fA fB f h : K) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«esZ_coeff» := P2M_Formalism_BasicNotions_Examples__NZ_esZ_coeff_fc48ec697a8a
