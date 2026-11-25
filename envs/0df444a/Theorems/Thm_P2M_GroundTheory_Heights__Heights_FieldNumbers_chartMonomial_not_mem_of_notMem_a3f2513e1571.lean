-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_not_mem_of_notMem_a3f2513e1571
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_not_mem_of_notMem_a3f2513e1571
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:52:01.784521+00:00
-- url     : https://prove2.me/theorems/347963a7-9ac5-5998-a1ed-dda51f2dbf8c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers chart Monomial not mem of not Mem a3f2513e1571: P2 M Ground Theory Heights  Heights Field Numbers chart Monomial not mem of not Mem a3f2513e1571
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers chart Monomial not mem of not Mem a3f2513e1571 construction uses the P2 M Ground Theory Heights  Heights Field Numbers chart Monomial not mem of not Mem a3f2513e1571 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LocalIntegralClosureChart.lean#L107-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LocalIntegralClosureChart.lean#L107-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
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
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_not_mem_of_notMem_a3f2513e1571 (W : Ideal (MRing ι F)) [W.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (b : K → ℕ) : chartMonomial u b ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«chartMonomial_not_mem_of_notMem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_not_mem_of_notMem_a3f2513e1571
