-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_disjoint_nonZeroDivisors_549f4b0b165b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_disjoint_nonZeroDivisors_549f4b0b165b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:50.764799+00:00
-- url     : https://prove2.me/theorems/00acfebb-4348-465f-8388-9dae16526c23
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Cycle Corresp disjoint non Zero Divisors 549f4b0b165b: P2 M Ground Theory Heights  Heights Numbers DVR Generic Cycle Corresp disjoint non Zero D
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Cycle Corresp disjoint non Zero Divisors 549f4b0b165b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Cycle Corresp disjoint non Zero Divisors 549f4b0b165b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericCycleCorresp.lean#L141-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericCycleCorresp.lean#L141-L152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
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
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericCycleCorresp
variable {K : Type*} {ι : K → Type*} {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_disjoint_nonZeroDivisors_549f4b0b165b {ϖ : O} (hϖ : Irreducible ϖ) (W : Ideal (MRing ι O)) [W.IsPrime]
    (hW : (C ϖ : MRing ι O) ∉ W) :
    Disjoint (((nonZeroDivisors O).map (C (σ := (Σ k, ι k)) (R := O)) : Submonoid (MRing ι O)) :
      Set (MRing ι O)) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericCycleCorresp».«disjoint_nonZeroDivisors» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_disjoint_nonZeroDivisors_549f4b0b165b
