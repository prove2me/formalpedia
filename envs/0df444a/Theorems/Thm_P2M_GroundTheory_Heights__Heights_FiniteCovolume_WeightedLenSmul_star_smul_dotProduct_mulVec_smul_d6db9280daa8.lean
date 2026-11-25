-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_star_smul_dotProduct_mulVec_smul_d6db9280daa8
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_star_smul_dotProduct_mulVec_smul_d6db9280daa8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:39:32.034541+00:00
-- url     : https://prove2.me/theorems/16862ee6-4599-404b-acf8-db1fa86dc9dd
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul star smul dot Product mul Vec smul d6db9280daa8: P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul star smul d
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul star smul dot Product mul Vec smul d6db9280daa8 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Weighted Len Smul star smul dot Product mul Vec smul d6db9280daa8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightedLenSmul.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightedLenSmul.lean#L30-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWeightedLenSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_star_smul_dotProduct_mulVec_smul_d6db9280daa8 (P : Matrix ι ι ℂ) (c : ℂ)
    (z : ι → ℂ) :
    star (c • z) ⬝ᵥ (P *ᵥ (c • z)) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (star z ⬝ᵥ (P *ᵥ z)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«WeightedLenSmul».«star_smul_dotProduct_mulVec_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_star_smul_dotProduct_mulVec_smul_d6db9280daa8
