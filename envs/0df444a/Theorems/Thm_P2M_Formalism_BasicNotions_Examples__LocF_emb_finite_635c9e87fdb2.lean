-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_emb_finite_635c9e87fdb2
-- name    : P2M_Formalism_BasicNotions_Examples__LocF_emb_finite_635c9e87fdb2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:55.807857+00:00
-- url     : https://prove2.me/theorems/5dba6b5d-8101-4c54-9193-505671bb6a09
-- title:
--   P2 M Formalism Basic Notions Examples  Loc F emb finite 635c9e87fdb2: P2 M Formalism Basic Notions Examples  Loc F emb finite 635c9e87fdb2
-- statement:
--   The P2 M Formalism Basic Notions Examples  Loc F emb finite 635c9e87fdb2 construction uses the P2 M Formalism Basic Notions Examples  Loc F emb finite 635c9e87fdb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L125-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean#L125-L142

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
open scoped TensorProduct

theorem P2M_Formalism_BasicNotions_Examples__LocF_emb_finite_635c9e87fdb2 : letI := (emb v l hv).toAlgebra
    FiniteDimensional ℚ_[l] (v.adicCompletion F) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LocF».«emb_finite» := P2M_Formalism_BasicNotions_Examples__LocF_emb_finite_635c9e87fdb2
