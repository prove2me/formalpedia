-- Prove2me | Theorems.Thm_ProbabilityTheory_entropy_le_log_card_of_mem_finite
-- name    : ProbabilityTheory.entropy_le_log_card_of_mem_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:03:06.540793+00:00
-- url     : https://prove2.me/theorems/32e0bc98-8d49-42f9-87af-0f61b70682bf
-- title:
--   Probability Theory: entropy le log card of mem finite
-- statement:
--   Entropy is at most the logarithm of the cardinality of a set in which X almost
--   surely takes
--   values in.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L113-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L113-L118

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

theorem ProbabilityTheory.entropy_le_log_card_of_mem_finite [DiscreteMeasurableSpace S]
    {A : Set S} {μ : Measure Ω} {X : Ω → S}
    (hA : A.Finite) (hX : Measurable X) (h : ∀ᵐ ω ∂μ, X ω ∈ A) :
    H[X; μ] ≤ log (Nat.card A) := by sorry
