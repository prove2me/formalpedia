-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_le_primeAbove_e4ed4df29902
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_le_primeAbove_e4ed4df29902
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:59.360839+00:00
-- url     : https://prove2.me/theorems/a15af3b4-c469-5479-9763-73cc2e66c873
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le le prime Above e4ed4df29902: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le le prime Above e4ed4df29902
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le le prime Above e4ed4df29902 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le le prime Above e4ed4df29902 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L203-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L203-L211

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_le_primeAbove_e4ed4df29902 [Fintype K] (hP : IsMultiHomogIdeal P) (hPW : P ≤ W) (hW : W.IsPrime)
    (hrel : IsRelevant W) (q : Ideal (homLocRing P W)) : P ≤ primeAbove hPW hW hrel q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingDimLe».«le_primeAbove» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_le_primeAbove_e4ed4df29902
