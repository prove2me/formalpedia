-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_expG_cont_48656f8a7b66
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_expG_cont_48656f8a7b66
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:47.714282+00:00
-- url     : https://prove2.me/theorems/ca42beb4-d669-40c5-9674-ea5fee2a7a53
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart exp G cont 48656f8a7b66: P2 M Formalism Basic Notions Examples  CD Chart exp G cont 48656f8a7b66
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart exp G cont 48656f8a7b66 construction uses the P2 M Formalism Basic Notions Examples  CD Chart exp G cont 48656f8a7b66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L38-L48

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open Formalism.BasicNotions.Examples₂.CD.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_expG_cont_48656f8a7b66 : Continuous C.expG := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«expG_cont» := P2M_Formalism_BasicNotions_Examples__CD_Chart_expG_cont_48656f8a7b66
