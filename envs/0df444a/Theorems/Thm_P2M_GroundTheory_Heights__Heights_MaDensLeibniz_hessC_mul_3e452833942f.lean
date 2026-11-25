-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_mul_3e452833942f
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_mul_3e452833942f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:48:08.367511+00:00
-- url     : https://prove2.me/theorems/48610c8b-0d8e-510c-903d-fcbdc3fa6e03
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Leibniz hess C mul 3e452833942f: P2 M Ground Theory Heights  Heights Ma Dens Leibniz hess C mul 3e452833942f
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Leibniz hess C mul 3e452833942f construction uses the P2 M Ground Theory Heights  Heights Ma Dens Leibniz hess C mul 3e452833942f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L44-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L44-L64

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

theorem P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_mul_3e452833942f (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (fun y => f y * g y) z =
      (f z : ℂ) • hessC g z + (g z : ℂ) • hessC f z + gradMat f g z + gradMat g f z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLeibniz».«hessC_mul» := P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_mul_3e452833942f
