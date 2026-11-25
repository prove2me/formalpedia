-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_sumElim_eq_dfad27be450d
-- name    : P2M_GroundTheory_Heights__Heights_det_gram_sumElim_eq_dfad27be450d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:44.266534+00:00
-- url     : https://prove2.me/theorems/ccc3dcd2-b8b7-41f2-bd6b-6fd8d3bd6ae9
-- title:
--   P2 M Ground Theory Heights  Heights det gram sum Elim eq dfad27be450d: P2 M Ground Theory Heights  Heights det gram sum Elim eq dfad27be450d
-- statement:
--   The P2 M Ground Theory Heights  Heights det gram sum Elim eq dfad27be450d construction uses the P2 M Ground Theory Heights  Heights det gram sum Elim eq dfad27be450d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L54-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L54-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem P2M_GroundTheory_Heights__Heights_det_gram_sumElim_eq_dfad27be450d {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → V) (u : κ → V) :
    det (gram ℂ (Sum.elim v u)) = det (gram ℂ v) *
      det (gram ℂ (fun j ↦ u j - (Submodule.span ℂ (Set.range v)).starProjection (u j))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_gram_sumElim_eq» := P2M_GroundTheory_Heights__Heights_det_gram_sumElim_eq_dfad27be450d
