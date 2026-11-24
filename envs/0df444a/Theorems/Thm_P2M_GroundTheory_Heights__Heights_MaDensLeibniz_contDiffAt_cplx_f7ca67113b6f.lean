-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_contDiffAt_cplx_f7ca67113b6f
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLeibniz_contDiffAt_cplx_f7ca67113b6f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:48.623966+00:00
-- url     : https://prove2.me/theorems/c7df321e-7017-4cae-a232-3d6812fb1d64
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Leibniz cont Diff At cplx f7ca67113b6f: P2 M Ground Theory Heights  Heights Ma Dens Leibniz cont Diff At cplx f7ca67113b6f
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Leibniz cont Diff At cplx f7ca67113b6f construction uses the P2 M Ground Theory Heights  Heights Ma Dens Leibniz cont Diff At cplx f7ca67113b6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L24-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLeibniz
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_MaDensLeibniz_contDiffAt_cplx_f7ca67113b6f {f : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f z) :
    ContDiffAt ℝ 2 (cplx f) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLeibniz».«contDiffAt_cplx» := P2M_GroundTheory_Heights__Heights_MaDensLeibniz_contDiffAt_cplx_f7ca67113b6f
