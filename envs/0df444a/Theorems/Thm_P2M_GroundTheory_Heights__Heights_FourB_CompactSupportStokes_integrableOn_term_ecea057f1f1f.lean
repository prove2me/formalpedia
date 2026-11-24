-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_term_ecea057f1f1f
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_term_ecea057f1f1f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:34.150248+00:00
-- url     : https://prove2.me/theorems/670d3af6-8ca1-413e-9a02-14992d29cb1c
-- title:
--   P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integrable On term ecea057f1f1f: P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integrable On term ecea057f1f1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integrable On term ecea057f1f1f construction uses the P2 M Ground Theory Heights  Heights Four B Compact Support Stokes integrable On term ecea057f1f1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L102-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/CompactSupportStokes.lean#L102-L122

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff Manifold
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_term_ecea057f1f1f (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (k j : Fin A.n) (w : X → ℝ)
    (hw : A.Smooth w) {L : Set X} (hL : IsCompact L) (hwL : tsupport w ⊆ L)
    (hLj : k = j ∨ L ⊆ (A.chart j).source) :
    IntegrableOn (fun y => χ.χ k ((A.chart j).symm y) * 1 *
      locDens A (Fin.cons (LocPot.ofFun w) Φ) j y) (A.chart j).target := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CompactSupportStokes».«integrableOn_term» := P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_term_ecea057f1f1f
