-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_proper_d65cdbdea1a5
-- name    : P2M_Formalism_BasicNotions_Examples__LocF_proper_d65cdbdea1a5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:48:25.658533+00:00
-- url     : https://prove2.me/theorems/71ea2dc1-8958-452a-bcdc-cdbb92966573
-- title:
--   P2 M Formalism Basic Notions Examples  Loc F proper d65cdbdea1a5: P2 M Formalism Basic Notions Examples  Loc F proper d65cdbdea1a5
-- statement:
--   The P2 M Formalism Basic Notions Examples  Loc F proper d65cdbdea1a5 construction uses the P2 M Formalism Basic Notions Examples  Loc F proper d65cdbdea1a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L20-L25

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

theorem P2M_Formalism_BasicNotions_Examples__LocF_proper_d65cdbdea1a5 : ProperSpace (v.adicCompletion F) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LocF».«proper» := P2M_Formalism_BasicNotions_Examples__LocF_proper_d65cdbdea1a5
