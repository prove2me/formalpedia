-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_Kernel_entropy_triple_add_entropy_le__04a239f82394
-- name    : P2M_ProbabilityTheory_Kernel_entropy_triple_add_entropy_le__04a239f82394
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:49:28.937737+00:00
-- url     : https://prove2.me/theorems/587ad455-b57e-41d2-b852-56fe4bcbf25f
-- title:
--   P2 M Probability Theory Kernel entropy triple add entropy le  04a239f82394: P2 M Probability Theory Kernel entropy triple add entropy le  04a239f82394
-- statement:
--   The submodularity inequality:
--   $$ H[X,Y,Z] + H[X] \leq H[X,Z] + H[X,Y].$$
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L365-L416
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L365-L416

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  [Countable V] [MeasurableSingletonClass V]

theorem P2M_ProbabilityTheory_Kernel_entropy_triple_add_entropy_le__04a239f82394
    {κ : Kernel T (S × U × V)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[κ, μ] + Hk[fst κ, μ] ≤ Hk[deleteMiddle κ, μ] + Hk[deleteRight κ, μ] := by sorry

alias «ProbabilityTheory».«Kernel».«entropy_triple_add_entropy_le'» := P2M_ProbabilityTheory_Kernel_entropy_triple_add_entropy_le__04a239f82394
