-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_SmoothIntegrals_contDiffOn_pd
-- name    : PositivityTheory.Rg.BcB.CG.SmoothIntegrals.contDiffOn_pd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:10.099962+00:00
-- url     : https://prove2.me/theorems/af972fd6-b154-4b15-809b-f04852e63c44
-- title:
--   Smooth Integrals: cont Diff On pd
-- statement:
--   The Smooth Integrals construction uses the cont Diff On pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PSmoothA.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PSmoothA.lean#L18-L27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PSmoothA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.CG.SmoothIntegrals
variable {X M T : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [TopologicalSpace T] [T2Space T] [MeasurableSpace T] [OpensMeasurableSpace T]
omit [FiniteDimensional ℝ X]

theorem PositivityTheory.Rg.BcB.CG.SmoothIntegrals.contDiffOn_pd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Q : X × M → V} {U : Set X} {W : Set M}
    (hU : IsOpen U) (hW : IsOpen W) (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) : ContDiffOn ℝ ∞ (pd Q) (U ×ˢ W) := by sorry
