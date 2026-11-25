-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_map_homFracDegZero_le_99e71cc4273e
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_map_homFracDegZero_le_99e71cc4273e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:14.575798+00:00
-- url     : https://prove2.me/theorems/f02c9133-f704-45dd-b684-67d8f615fb1e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers map hom Frac Deg Zero le 99e71cc4273e: P2 M Ground Theory Heights  Heights Field Numbers map hom Frac Deg Zero le 99e71cc4273e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers map hom Frac Deg Zero le 99e71cc4273e construction uses the P2 M Ground Theory Heights  Heights Field Numbers map hom Frac Deg Zero le 99e71cc4273e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L138-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L138-L146

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_map_homFracDegZero_le_99e71cc4273e (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«map_homFracDegZero_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_map_homFracDegZero_le_99e71cc4273e
