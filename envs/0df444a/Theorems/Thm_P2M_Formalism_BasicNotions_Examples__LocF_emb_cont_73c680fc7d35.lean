-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_emb_cont_73c680fc7d35
-- name    : P2M_Formalism_BasicNotions_Examples__LocF_emb_cont_73c680fc7d35
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:46:59.999885+00:00
-- url     : https://prove2.me/theorems/0d5e91b4-bc79-4cea-a80a-329cf55dfb06
-- title:
--   P2 M Formalism Basic Notions Examples  Loc F emb cont 73c680fc7d35: P2 M Formalism Basic Notions Examples  Loc F emb cont 73c680fc7d35
-- statement:
--   The P2 M Formalism Basic Notions Examples  Loc F emb cont 73c680fc7d35 construction uses the P2 M Formalism Basic Notions Examples  Loc F emb cont 73c680fc7d35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L121-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L121-L122

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb

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
variable (l : ℕ) [hl : Fact l.Prime] (hv : (l : 𝓞 F) ∈ v.asIdeal)

theorem P2M_Formalism_BasicNotions_Examples__LocF_emb_cont_73c680fc7d35 : Continuous (emb v l hv) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LocF».«emb_cont» := P2M_Formalism_BasicNotions_Examples__LocF_emb_cont_73c680fc7d35
