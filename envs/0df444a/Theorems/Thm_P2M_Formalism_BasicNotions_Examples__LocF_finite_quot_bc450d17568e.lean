-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_finite_quot_bc450d17568e
-- name    : P2M_Formalism_BasicNotions_Examples__LocF_finite_quot_bc450d17568e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:05.115627+00:00
-- url     : https://prove2.me/theorems/977f8bc1-d102-4602-8ba3-ffe30d46a462
-- title:
--   P2 M Formalism Basic Notions Examples  Loc F finite quot bc450d17568e: P2 M Formalism Basic Notions Examples  Loc F finite quot bc450d17568e
-- statement:
--   The P2 M Formalism Basic Notions Examples  Loc F finite quot bc450d17568e construction uses the P2 M Formalism Basic Notions Examples  Loc F finite quot bc450d17568e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L18-L18

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LocF
open NumberField IsDedekindDomain HeightOneSpectrum WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem P2M_Formalism_BasicNotions_Examples__LocF_finite_quot_bc450d17568e : Finite (𝓞 F ⧸ v.asIdeal) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LocF».«finite_quot» := P2M_Formalism_BasicNotions_Examples__LocF_finite_quot_bc450d17568e
