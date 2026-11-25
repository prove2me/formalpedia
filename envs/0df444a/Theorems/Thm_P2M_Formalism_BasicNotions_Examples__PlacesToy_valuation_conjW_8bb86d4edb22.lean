-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_valuation_conjW_8bb86d4edb22
-- name    : P2M_Formalism_BasicNotions_Examples__PlacesToy_valuation_conjW_8bb86d4edb22
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:36.25339+00:00
-- url     : https://prove2.me/theorems/ddeb55f7-459d-4e55-8c9c-bc04413c781e
-- title:
--   P2 M Formalism Basic Notions Examples  Places Toy valuation conj W 8bb86d4edb22: P2 M Formalism Basic Notions Examples  Places Toy valuation conj W 8bb86d4edb22
-- statement:
--   The P2 M Formalism Basic Notions Examples  Places Toy valuation conj W 8bb86d4edb22 construction uses the P2 M Formalism Basic Notions Examples  Places Toy valuation conj W 8bb86d4edb22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L275-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L275-L285

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

theorem P2M_Formalism_BasicNotions_Examples__PlacesToy_valuation_conjW_8bb86d4edb22 (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    (conjW w).valuation K x = w.valuation K (star x) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«PlacesToy».«valuation_conjW» := P2M_Formalism_BasicNotions_Examples__PlacesToy_valuation_conjW_8bb86d4edb22
