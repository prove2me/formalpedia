-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_trdeg_eq_of_le_of_isAlgebraic_983b32a504c5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_trdeg_eq_of_le_of_isAlgebraic_983b32a504c5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:59.546487+00:00
-- url     : https://prove2.me/theorems/cf88d013-a559-476c-a3b6-7a9a3fbf4d68
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field trdeg eq of le of is Algebraic 983b32a504c5: P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field trdeg eq of le of i
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field trdeg eq of le of is Algebraic 983b32a504c5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field trdeg eq of le of is Algebraic 983b32a504c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PConeTrdegFnField.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PConeTrdegFnField.lean#L13-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConeTrdegFnField
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_trdeg_eq_of_le_of_isAlgebraic_983b32a504c5 {O B : Type} [CommRing O] [IsDomain O] [CommRing B]
    [IsDomain B] [Algebra O B] (hinj : Function.Injective (algebraMap O B)) {S T : Subalgebra O B}
    (hST : S ≤ T) (halg : ∀ t ∈ T, IsAlgebraic S t) : Algebra.trdeg O S = Algebra.trdeg O T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ConeTrdegFnField».«trdeg_eq_of_le_of_isAlgebraic» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_trdeg_eq_of_le_of_isAlgebraic_983b32a504c5
