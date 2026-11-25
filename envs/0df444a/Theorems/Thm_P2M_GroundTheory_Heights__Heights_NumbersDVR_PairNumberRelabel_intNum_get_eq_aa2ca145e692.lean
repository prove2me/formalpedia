-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_intNum_get_eq_aa2ca145e692
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_intNum_get_eq_aa2ca145e692
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:02:25.766424+00:00
-- url     : https://prove2.me/theorems/0bce5bb6-4da8-416a-a3e6-0698cedb7239
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel int Num get eq aa2ca145e692: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel int Num get eq aa2ca145e692
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel int Num get eq aa2ca145e692 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel int Num get eq aa2ca145e692 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L128-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
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
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_intNum_get_eq_aa2ca145e692 {F : Type*} [Field F] (I : Ideal (MRing ι F)) (l : List (K → ℤ)) :
    intNum F I l.get = eventualValue (l.foldr diffStep (hilbFn I)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«intNum_get_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_intNum_get_eq_aa2ca145e692
