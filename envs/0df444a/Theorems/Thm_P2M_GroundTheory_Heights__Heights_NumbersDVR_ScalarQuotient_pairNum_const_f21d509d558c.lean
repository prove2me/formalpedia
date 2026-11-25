-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_pairNum_const_f21d509d558c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_pairNum_const_f21d509d558c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:17.621511+00:00
-- url     : https://prove2.me/theorems/8996d751-ffc8-4381-9b32-30d755a1a450
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient pair Num const f21d509d558c: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient pair Num const f21d509d558c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient pair Num const f21d509d558c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient pair Num const f21d509d558c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L174-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L174-L194

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
variable [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_pairNum_const_f21d509d558c (P : Ideal (MRing ι O)) [P.IsPrime]
    (hP : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P) {ϖ : O} (hϖ : ϖ ≠ 0) (u : Oˣ) (n : ℕ)
    {N : ℕ} (x : Fin N → K → ℤ) (k : ℕ) (Q : List (K → ℤ)) :
    pairNum P x x (fun _ => C ((u : O) * ϖ ^ n)) (fun _ => 1) (psumExpansion N k) Q =
      (k : ℤ) * n * cycEval (fun W => classNum x (psum (Fin N) ℤ (k - 1)) Q W)
        (divCycle P (C ϖ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«pairNum_const» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_pairNum_const_f21d509d558c
