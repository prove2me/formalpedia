-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_mem_conjW_pow_c73c9fbba4a3
-- name    : P2M_Formalism_BasicNotions_Examples__PlacesToy_mem_conjW_pow_c73c9fbba4a3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:39.868867+00:00
-- url     : https://prove2.me/theorems/14a30edf-1b32-4c11-9329-1f038c565bf1
-- title:
--   P2 M Formalism Basic Notions Examples  Places Toy mem conj W pow c73c9fbba4a3: P2 M Formalism Basic Notions Examples  Places Toy mem conj W pow c73c9fbba4a3
-- statement:
--   The P2 M Formalism Basic Notions Examples  Places Toy mem conj W pow c73c9fbba4a3 construction uses the P2 M Formalism Basic Notions Examples  Places Toy mem conj W pow c73c9fbba4a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L243-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L243-L245

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions.Examples₂.PlacesToy
variable {K : Type} [Field K] [NumberField K] [StarRing K]
omit [NumberField K]

theorem P2M_Formalism_BasicNotions_Examples__PlacesToy_mem_conjW_pow_c73c9fbba4a3 (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (n : ℕ) :
    r ∈ (conjW w).asIdeal ^ n ↔ starO r ∈ w.asIdeal ^ n := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«PlacesToy».«mem_conjW_pow» := P2M_Formalism_BasicNotions_Examples__PlacesToy_mem_conjW_pow_c73c9fbba4a3
