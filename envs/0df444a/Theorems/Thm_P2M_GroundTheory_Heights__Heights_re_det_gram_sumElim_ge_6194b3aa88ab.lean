-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_re_det_gram_sumElim_ge_6194b3aa88ab
-- name    : P2M_GroundTheory_Heights__Heights_re_det_gram_sumElim_ge_6194b3aa88ab
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:50.342564+00:00
-- url     : https://prove2.me/theorems/ee69d50d-0021-4291-9d5a-326ca2207bcf
-- title:
--   P2 M Ground Theory Heights  Heights re det gram sum Elim ge 6194b3aa88ab: P2 M Ground Theory Heights  Heights re det gram sum Elim ge 6194b3aa88ab
-- statement:
--   The P2 M Ground Theory Heights  Heights re det gram sum Elim ge 6194b3aa88ab construction uses the P2 M Ground Theory Heights  Heights re det gram sum Elim ge 6194b3aa88ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L151-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L151-L166

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

theorem P2M_GroundTheory_Heights__Heights_re_det_gram_sumElim_ge_6194b3aa88ab {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (W : Submodule ℂ V) [W.HasOrthogonalProjection] (v : ι → V) (hv : ∀ i, v i ∈ W) (u : κ → V) :
    (det (gram ℂ v)).re * (det (gram ℂ fun j ↦ Wᗮ.starProjection (u j))).re ≤
      (det (gram ℂ (Sum.elim v u))).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«re_det_gram_sumElim_ge» := P2M_GroundTheory_Heights__Heights_re_det_gram_sumElim_ge_6194b3aa88ab
