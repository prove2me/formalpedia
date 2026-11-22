-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_mat_expG_1363518d9b59
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_mat_expG_1363518d9b59
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:27:21.699966+00:00
-- url     : https://prove2.me/theorems/384d90c9-fab9-4ec0-9229-ba9d902bef2e
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart mat exp G 1363518d9b59: P2 M Formalism Basic Notions Examples  CD Chart mat exp G 1363518d9b59
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart mat exp G 1363518d9b59 construction uses the P2 M Formalism Basic Notions Examples  CD Chart mat exp G 1363518d9b59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L25-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L25-L25

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

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_mat_expG_1363518d9b59 (X : V) : C.mat (C.expG X) = exp (X : 𝔸) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«mat_expG» := P2M_Formalism_BasicNotions_Examples__CD_Chart_mat_expG_1363518d9b59
