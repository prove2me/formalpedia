-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_standard_inner_pt_f585a90ab32d
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_standard_inner_pt_f585a90ab32d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:42.664268+00:00
-- url     : https://prove2.me/theorems/4b100b14-ebc2-5351-b88b-4dcb21b90304
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt standard inner pt f585a90ab32d: P2 M Ground Theory Heights  Theta Functional Equation Alt standard inner pt f585a90ab32d
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt standard inner pt f585a90ab32d construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt standard inner pt f585a90ab32d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean#L452-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean#L452-L460

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ChainWittIndexHypothesesMet
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_MemRangeIffIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open NumberField TensorProduct Module GroundTheory.Automorphic
open scoped nonZeroDivisors
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open CAt
attribute [instance] MetSpace.instAddCommGroup MetSpace.instModule MetSpace.instFD
  MetSpace.instModuleO MetSpace.instTower
variable {E : Type} [Field E] [NumberField E]
variable (E) (n : ℕ)
variable {E n}
variable (E n)
variable {E n}

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_standard_inner_pt_f585a90ab32d (τ : InfinitePlace E) (v w : Fin n → E) :
    inner ℂ ((MetSpace.standard E n).pt τ v) ((MetSpace.standard E n).pt τ w) =
      ∑ i, starRingEnd ℂ (τ.embedding (v i)) * τ.embedding (w i) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«standard_inner_pt» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_standard_inner_pt_f585a90ab32d
