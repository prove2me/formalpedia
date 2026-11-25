-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_multiHomog_c779affea215
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_multiHomog_c779affea215
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:07:34.411094+00:00
-- url     : https://prove2.me/theorems/5b9d7931-5b48-4831-b95c-07a828d3252f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le prime Above multi Homog c779affea215: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le prime Above multi Homog c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le prime Above multi Homog c779affea215 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le prime Above multi Homog c779affea215 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L163-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L163-L174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
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
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_multiHomog_c779affea215 [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W)
    (q : Ideal (homLocRing P W)) : IsMultiHomogIdeal (primeAbove hPW hW hrel q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingDimLe».«primeAbove_multiHomog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_multiHomog_c779affea215
