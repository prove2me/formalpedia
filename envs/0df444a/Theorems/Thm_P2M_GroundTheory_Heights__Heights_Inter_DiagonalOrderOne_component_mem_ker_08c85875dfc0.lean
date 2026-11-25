-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_component_mem_ker_08c85875dfc0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_component_mem_ker_08c85875dfc0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:58.329494+00:00
-- url     : https://prove2.me/theorems/8c80ca8f-b324-59a9-80c2-8c3d3866b33f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Order One component mem ker 08c85875dfc0: P2 M Ground Theory Heights  Heights Inter Diagonal Order One component mem ker 08c85875dfc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Order One component mem ker 08c85875dfc0 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Order One component mem ker 08c85875dfc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrdOne.lean#L89-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrdOne.lean#L89-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrdOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOrderOne
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_component_mem_ker_08c85875dfc0 (c : (Σ k, ι k) → Φ) {f : MRing ι} (hf : f ∈ RingHom.ker (T.multiConeMap c))
    (m : K → ℕ) :
    weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) m f ∈
      RingHom.ker (T.multiConeMap c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOrderOne».«component_mem_ker» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_component_mem_ker_08c85875dfc0
