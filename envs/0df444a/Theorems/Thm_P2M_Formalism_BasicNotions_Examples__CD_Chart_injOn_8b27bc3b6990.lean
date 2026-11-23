-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_injOn_8b27bc3b6990
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_injOn_8b27bc3b6990
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:52.136797+00:00
-- url     : https://prove2.me/theorems/32b5ebc3-b24d-4f32-8101-afe1543f8393
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart inj On 8b27bc3b6990: P2 M Formalism Basic Notions Examples  CD Chart inj On 8b27bc3b6990
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart inj On 8b27bc3b6990 construction uses the P2 M Formalism Basic Notions Examples  CD Chart inj On 8b27bc3b6990 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L58-L65

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
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
include hR

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_injOn_8b27bc3b6990 : InjOn C.expG (ball (0 : V) ρ) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«injOn» := P2M_Formalism_BasicNotions_Examples__CD_Chart_injOn_8b27bc3b6990
