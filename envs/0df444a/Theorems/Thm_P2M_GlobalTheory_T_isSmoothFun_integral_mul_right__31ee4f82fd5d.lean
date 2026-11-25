-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isSmoothFun_integral_mul_right__31ee4f82fd5d
-- name    : P2M_GlobalTheory_T_isSmoothFun_integral_mul_right__31ee4f82fd5d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:37:50.866282+00:00
-- url     : https://prove2.me/theorems/36a42c48-3d87-4c09-ad5b-0794387f286b
-- title:
--   P2 M Global Theory T is Smooth Fun integral mul right  31ee4f82fd5d: P2 M Global Theory T is Smooth Fun integral mul right  31ee4f82fd5d
-- statement:
--   The P2 M Global Theory T is Smooth Fun integral mul right  31ee4f82fd5d construction uses the P2 M Global Theory T is Smooth Fun integral mul right  31ee4f82fd5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothFunIntegralMulRightStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothFunIntegralMulRightStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRight
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRightStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_isSmoothFun_integral_mul_right__31ee4f82fd5d : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] (K : Set G), IsCompact K → ν Kᶜ = 0 → ∀ κ : G → ℂ, h.IsSmoothFun κ → h.IsSmoothFun (fun z => ∫ y, κ (z * y) ∂ν) := by sorry

alias «GlobalTheory».«T».«isSmoothFun_integral_mul_right'» := P2M_GlobalTheory_T_isSmoothFun_integral_mul_right__31ee4f82fd5d
