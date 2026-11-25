-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_sq_half_cccea07f6850
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_sq_half_cccea07f6850
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:49:13.459914+00:00
-- url     : https://prove2.me/theorems/87216469-eadc-4efb-b6a2-796965e5ea18
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Leibniz dzb cplx sq half cccea07f6850: P2 M Ground Theory Heights  Heights Ma Dens Leibniz dzb cplx sq half cccea07f6850
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Leibniz dzb cplx sq half cccea07f6850 construction uses the P2 M Ground Theory Heights  Heights Ma Dens Leibniz dzb cplx sq half cccea07f6850 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L36-L42

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

theorem P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_sq_half_cccea07f6850 (k : Fin D) (f : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) :
    dzb k (cplx fun x => f x ^ 2 / 2) y = cplx f y * dzb k (cplx f) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLeibniz».«dzb_cplx_sq_half» := P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_sq_half_cccea07f6850
