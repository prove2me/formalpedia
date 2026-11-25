-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_pt_mem_conePts_b7c8ef543411
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_pt_mem_conePts_b7c8ef543411
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:17:24.67483+00:00
-- url     : https://prove2.me/theorems/e5898bd4-8674-46bf-bf2d-603f3d99f61a
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite pt mem cone Pts b7c8ef543411: P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite pt mem cone Pt
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite pt mem cone Pts b7c8ef543411 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Component Res Fibre Finite pt mem cone Pts b7c8ef543411 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComponentResFibreFinite.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComponentResFibreFinite.lean#L22-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComponentResFibreFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_pt_mem_conePts_b7c8ef543411 (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e) (x : R.R.M) :
    R.pt x ∈ ReciprocityTheory.AnForm.R.conePts W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ComponentResFibreFinite».«pt_mem_conePts» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_pt_mem_conePts_b7c8ef543411
