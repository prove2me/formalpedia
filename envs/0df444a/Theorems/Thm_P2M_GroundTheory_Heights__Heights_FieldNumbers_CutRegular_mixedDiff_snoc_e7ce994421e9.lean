-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_mixedDiff_snoc_e7ce994421e9
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_mixedDiff_snoc_e7ce994421e9
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:48.202334+00:00
-- url     : https://prove2.me/theorems/5ca3f7a6-250b-4049-877d-b095e3ffb59e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular mixed Diff snoc e7ce994421e9: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular mixed Diff snoc e7ce994421e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular mixed Diff snoc e7ce994421e9 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular mixed Diff snoc e7ce994421e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L22-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
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
open GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_mixedDiff_snoc_e7ce994421e9 {n : ℕ} (bs : Fin n → K → ℤ) (c : K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Fin.snoc (α := fun _ => K → ℤ) bs c) h = mixedDiff bs (diffStep c h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«mixedDiff_snoc» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_mixedDiff_snoc_e7ce994421e9
