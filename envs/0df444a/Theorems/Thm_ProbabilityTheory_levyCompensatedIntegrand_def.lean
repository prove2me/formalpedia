-- Prove2me | Theorems.Thm_ProbabilityTheory_levyCompensatedIntegrand_def
-- name    : ProbabilityTheory.levyCompensatedIntegrand_def
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:14:27.273175+00:00
-- url     : https://prove2.me/theorems/52c87599-8f91-49b9-93bc-d21ec304439e
-- title:
--   LeanLevy: ProbabilityTheory.levyCompensatedIntegrand_def
-- statement:
--   The **compensated integrand** for the Lévy-Khintchine formula: Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4//home/willr/projects/Prove2Me/scratch/leanlevy_bulk_20261027/source/LeanLevy/Levy/CompensatedIntegral.lean#L42

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

theorem ProbabilityTheory.levyCompensatedIntegrand_def : ∀ (ξ x : Real),
  @Eq Complex (ProbabilityTheory.levyCompensatedIntegrand ξ x)
    (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub)
      (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub)
        (Complex.exp
          (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
            (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) ↑x ↑ξ) Complex.I))
        (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
      (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
        (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
          (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) ↑x ↑ξ) Complex.I)
        (@ite Complex
          (@LT.lt Real Real.instLT (@abs Real Real.lattice Real.instAddGroup x)
            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
          ((@abs Real Real.lattice Real.instAddGroup x).decidableLT
            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@OfNat.ofNat Complex (nat_lit 0) (@Zero.toOfNat0 Complex Complex.instZero))))) := by sorry
