-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_img_eq_2b325c8b99f9
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_img_eq_2b325c8b99f9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:43.401831+00:00
-- url     : https://prove2.me/theorems/83ff00d6-5d41-449f-8c9c-7dd9335f5f92
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart img eq 2b325c8b99f9: P2 M Formalism Basic Notions Examples  CD Chart img eq 2b325c8b99f9
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart img eq 2b325c8b99f9 construction uses the P2 M Formalism Basic Notions Examples  CD Chart img eq 2b325c8b99f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L29-L36

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

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_img_eq_2b325c8b99f9 (s : Set V) : C.img s = C.expG '' s := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«img_eq» := P2M_Formalism_BasicNotions_Examples__CD_Chart_img_eq_2b325c8b99f9
