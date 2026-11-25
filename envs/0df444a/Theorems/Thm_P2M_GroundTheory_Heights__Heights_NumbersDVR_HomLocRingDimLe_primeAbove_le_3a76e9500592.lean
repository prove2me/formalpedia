-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_le_3a76e9500592
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_le_3a76e9500592
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:44.809877+00:00
-- url     : https://prove2.me/theorems/e9c2cd4b-2c6a-4494-a105-9fbca5d4bb25
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le prime Above le 3a76e9500592: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le prime Above le 3a76e9500592
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le prime Above le 3a76e9500592 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le prime Above le 3a76e9500592 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L213-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L213-L229

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_le_3a76e9500592 [Fintype K] (hloc : HomLocRingIsLocal.Statement.{u}) (hPW : P ≤ W)
    (hW : W.IsPrime) (hrel : IsRelevant W) (q : Ideal (homLocRing P W)) [hq : q.IsPrime] :
    primeAbove hPW hW hrel q ≤ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingDimLe».«primeAbove_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_le_3a76e9500592
