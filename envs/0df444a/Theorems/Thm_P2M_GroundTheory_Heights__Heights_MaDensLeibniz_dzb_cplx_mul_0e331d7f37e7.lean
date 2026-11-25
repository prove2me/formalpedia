-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_mul_0e331d7f37e7
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_mul_0e331d7f37e7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:48:01.788574+00:00
-- url     : https://prove2.me/theorems/e5454bb1-9c8d-5dc4-98d0-2245afe3db1d
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Leibniz dzb cplx mul 0e331d7f37e7: P2 M Ground Theory Heights  Heights Ma Dens Leibniz dzb cplx mul 0e331d7f37e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Leibniz dzb cplx mul 0e331d7f37e7 construction uses the P2 M Ground Theory Heights  Heights Ma Dens Leibniz dzb cplx mul 0e331d7f37e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLeibniz.lean#L30-L34

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

theorem P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_mul_0e331d7f37e7 (k : Fin D) (f g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx fun x => f x * g x) y = cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLeibniz».«dzb_cplx_mul» := P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_mul_0e331d7f37e7
