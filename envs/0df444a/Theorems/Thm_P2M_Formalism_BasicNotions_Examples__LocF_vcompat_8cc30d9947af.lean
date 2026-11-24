-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_vcompat_8cc30d9947af
-- name    : P2M_Formalism_BasicNotions_Examples__LocF_vcompat_8cc30d9947af
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:09.191566+00:00
-- url     : https://prove2.me/theorems/e282fa10-dd38-4a7f-8395-791e95bb3e24
-- title:
--   P2 M Formalism Basic Notions Examples  Loc F vcompat 8cc30d9947af: P2 M Formalism Basic Notions Examples  Loc F vcompat 8cc30d9947af
-- statement:
--   The P2 M Formalism Basic Notions Examples  Loc F vcompat 8cc30d9947af construction uses the P2 M Formalism Basic Notions Examples  Loc F vcompat 8cc30d9947af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L15-L16

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

theorem P2M_Formalism_BasicNotions_Examples__LocF_vcompat_8cc30d9947af : letI := vrel v
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Compatible := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LocF».«vcompat» := P2M_Formalism_BasicNotions_Examples__LocF_vcompat_8cc30d9947af
