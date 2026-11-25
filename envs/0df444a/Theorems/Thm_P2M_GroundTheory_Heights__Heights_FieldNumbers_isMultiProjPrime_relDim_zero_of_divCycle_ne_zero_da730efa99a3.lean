-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_relDim_zero_of_divCycle_ne_zero_da730efa99a3
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_relDim_zero_of_divCycle_ne_zero_da730efa99a3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:03.424361+00:00
-- url     : https://prove2.me/theorems/96682680-6812-497e-993c-2aca8a92c460
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Multi Proj Prime rel Dim zero of div Cycle ne zero da730efa99a3: P2 M Ground Theory Heights  Heights Field Numbers is Multi Proj Prime rel Dim zero
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Multi Proj Prime rel Dim zero of div Cycle ne zero da730efa99a3 construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Multi Proj Prime rel Dim zero of div Cycle ne zero da730efa99a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDivPrincipalDegree.lean#L36-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDivPrincipalDegree.lean#L36-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivPrincipalDegree
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
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_relDim_zero_of_divCycle_ne_zero_da730efa99a3 {P : Ideal (MRing ι F)}
    (hP : IsMultiProjPrime P) (hdim : relDim P = 1) {b : K → ℕ} {f : MRing ι F}
    (hf : IsMultiHomog f b) (hfP : f ∉ P) {W : Ideal (MRing ι F)} (hW : divCycle P f W ≠ 0) :
    IsMultiProjPrime W ∧ relDim W = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isMultiProjPrime_relDim_zero_of_divCycle_ne_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_relDim_zero_of_divCycle_ne_zero_da730efa99a3
