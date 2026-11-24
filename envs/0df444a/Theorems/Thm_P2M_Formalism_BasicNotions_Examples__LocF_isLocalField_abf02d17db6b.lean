-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_isLocalField_abf02d17db6b
-- name    : P2M_Formalism_BasicNotions_Examples__LocF_isLocalField_abf02d17db6b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:40:53.8161+00:00
-- url     : https://prove2.me/theorems/fa0f41b8-2081-47fa-b97d-4b8feca571c5
-- title:
--   P2 M Formalism Basic Notions Examples  Loc F is Local Field abf02d17db6b: P2 M Formalism Basic Notions Examples  Loc F is Local Field abf02d17db6b
-- statement:
--   The P2 M Formalism Basic Notions Examples  Loc F is Local Field abf02d17db6b construction uses the P2 M Formalism Basic Notions Examples  Loc F is Local Field abf02d17db6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L27-L37

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

theorem P2M_Formalism_BasicNotions_Examples__LocF_isLocalField_abf02d17db6b : letI := vrel v; IsNonarchimedeanLocalField (v.adicCompletion F) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LocF».«isLocalField» := P2M_Formalism_BasicNotions_Examples__LocF_isLocalField_abf02d17db6b
