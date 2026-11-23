-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_rho_2d4d0a8259f7
-- name    : P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_rho_2d4d0a8259f7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:42.439453+00:00
-- url     : https://prove2.me/theorems/89624133-8a1e-4410-8935-4514d3e9ff02
-- title:
--   P2 M Formalism Basic Notions Examples  CD Chart exists rho 2d4d0a8259f7: P2 M Formalism Basic Notions Examples  CD Chart exists rho 2d4d0a8259f7
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD Chart exists rho 2d4d0a8259f7 construction uses the P2 M Formalism Basic Notions Examples  CD Chart exists rho 2d4d0a8259f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean#L50-L53

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

theorem P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_rho_2d4d0a8259f7 : ∃ ρ > 0, ∀ Z : 𝔸, ‖Z‖ < ρ →
    logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«Chart».«exists_rho» := P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_rho_2d4d0a8259f7
