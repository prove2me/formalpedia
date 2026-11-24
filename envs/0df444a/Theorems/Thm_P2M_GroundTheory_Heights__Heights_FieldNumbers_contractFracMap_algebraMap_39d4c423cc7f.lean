-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_algebraMap_39d4c423cc7f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_algebraMap_39d4c423cc7f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:41.83184+00:00
-- url     : https://prove2.me/theorems/9f960e68-2ea5-40c5-8c0e-0331b54bc3e0
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers contract Frac Map algebra Map 39d4c423cc7f: P2 M Ground Theory Heights  Heights Field Numbers contract Frac Map algebra Map 39d4c423cc7f
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers contract Frac Map algebra Map 39d4c423cc7f construction uses the P2 M Ground Theory Heights  Heights Field Numbers contract Frac Map algebra Map 39d4c423cc7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L126-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L126-L136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
variable [DecidableEq K] [DecidableEq K']
variable {F : Type u} [Field F]
omit [DecidableEq K] [DecidableEq K']

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_algebraMap_39d4c423cc7f (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (a : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') a)) =
      algebraMap _ (FractionRing (MRing ι' F ⧸ P'))
        (Ideal.Quotient.mk P' (rename (blockIncl j ι') a)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«contractFracMap_algebraMap» := P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_algebraMap_39d4c423cc7f
