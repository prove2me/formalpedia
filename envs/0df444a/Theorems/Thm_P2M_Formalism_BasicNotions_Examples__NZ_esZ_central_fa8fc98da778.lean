-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_esZ_central_fa8fc98da778
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_esZ_central_fa8fc98da778
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:58.033919+00:00
-- url     : https://prove2.me/theorems/9cc06be8-591b-49de-90ab-01a7af87ba40
-- title:
--   P2 M Formalism Basic Notions Examples  NZ es Z central fa8fc98da778: P2 M Formalism Basic Notions Examples  NZ es Z central fa8fc98da778
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ es Z central fa8fc98da778 construction uses the P2 M Formalism Basic Notions Examples  NZ es Z central fa8fc98da778 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L157-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L157-L162

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
omit [CharZero K]

theorem P2M_Formalism_BasicNotions_Examples__NZ_esZ_central_fa8fc98da778 (f : Λ) (a) : esZ K Γ fA fB f * a = a * esZ K Γ fA fB f := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«esZ_central» := P2M_Formalism_BasicNotions_Examples__NZ_esZ_central_fa8fc98da778
