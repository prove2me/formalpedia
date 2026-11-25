-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_eq_9d5a3e5ca313
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_eq_9d5a3e5ca313
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:15:57.509565+00:00
-- url     : https://prove2.me/theorems/a5df540d-a4fd-5d9b-aa47-6922e2740d98
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L eq 9d5a3e5ca313: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L eq 9d5a3e5ca313
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L eq 9d5a3e5ca313 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L eq 9d5a3e5ca313 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L112-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
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
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
variable {K : Type*} [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_eq_9d5a3e5ca313 {ι : K → Type*} (F : Type*) [Field F] (P : Ideal (MRing ι F))
    (l : List (K → ℤ)) : intNumL F P l = eventualValue (l.foldr diffStep (hilbFn P)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«intNumL_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_eq_9d5a3e5ca313
