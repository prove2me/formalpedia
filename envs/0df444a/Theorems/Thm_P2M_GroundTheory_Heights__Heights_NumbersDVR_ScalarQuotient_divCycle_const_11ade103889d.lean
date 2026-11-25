-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_const_11ade103889d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_const_11ade103889d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:08:15.695609+00:00
-- url     : https://prove2.me/theorems/308e67c5-d47f-4f11-8e8e-b11c46197751
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle const 11ade103889d: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle const 11ade103889d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle const 11ade103889d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle const 11ade103889d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L130-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L130-L145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
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
open GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_const_11ade103889d (P : Ideal (MRing ι O)) [P.IsPrime]
    (hP : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P) {ϖ : O} (hϖ : ϖ ≠ 0) (u : Oˣ) (n : ℕ) :
    divCycle P (C ((u : O) * ϖ ^ n)) = fun W => (n : ℤ) * divCycle P (C ϖ) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«divCycle_const» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_const_11ade103889d
