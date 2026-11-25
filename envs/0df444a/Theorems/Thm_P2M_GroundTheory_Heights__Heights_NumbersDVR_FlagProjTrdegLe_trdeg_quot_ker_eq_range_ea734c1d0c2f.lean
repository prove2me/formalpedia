-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_quot_ker_eq_range_ea734c1d0c2f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_quot_ker_eq_range_ea734c1d0c2f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:11:02.60816+00:00
-- url     : https://prove2.me/theorems/cddf7f9e-6f6e-47bf-8ec2-994f656f9905
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg quot ker eq range ea734c1d0c2f: P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg quot ker eq range ea73
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg quot ker eq range ea734c1d0c2f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg quot ker eq range ea734c1d0c2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean#L16-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagProjTrdegLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_quot_ker_eq_range_ea734c1d0c2f {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
    [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) (hg : Function.Injective g) :
    Algebra.trdeg R (A ⧸ RingHom.ker f) = Algebra.trdeg R (g.comp f).range := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagProjTrdegLe».«trdeg_quot_ker_eq_range» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_quot_ker_eq_range_ea734c1d0c2f
