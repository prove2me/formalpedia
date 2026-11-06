-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_levyCompensatedIntegrand_eq_small_add_large
-- name    : ProbabilityTheory.integral_levyCompensatedIntegrand_eq_small_add_large
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:22:52.836924+00:00
-- url     : https://prove2.me/theorems/9afb2b4a-383c-4828-b825-7a5909a5e434
-- title:
--   LeanLevy: ProbabilityTheory.integral_levyCompensatedIntegrand_eq_small_add_large
-- statement:
--   The Lévy–Khintchine jump integral splits at radius 1: the compensated part over Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CompensatedIntegral.lean#L171

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

theorem ProbabilityTheory.integral_levyCompensatedIntegrand_eq_small_add_large : ∀ {ν : @MeasureTheory.Measure Real Real.measurableSpace},
  ProbabilityTheory.IsLevyMeasure ν →
    ∀ (ξ : Real),
      @Eq Complex
        (@MeasureTheory.integral Real Complex Complex.instNormedAddCommGroup
          (@NormedSpace.complexToReal Complex
            (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
            (@NormedField.toNormedSpace Complex Complex.instNormedField))
          Real.measurableSpace ν fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x)
        (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd)
          (@MeasureTheory.integral Real Complex Complex.instNormedAddCommGroup
            (@NormedSpace.complexToReal Complex
              (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
              (@NormedField.toNormedSpace Complex Complex.instNormedField))
            Real.measurableSpace
            (@MeasureTheory.Measure.restrict Real Real.measurableSpace ν
              (@Set.Ioo Real Real.instPreorder
                (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))))
            fun x =>
            @HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub)
              (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub)
                (Complex.exp
                  (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                    (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) ↑x ↑ξ) Complex.I))
                (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
              (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) ↑x ↑ξ) Complex.I))
          (@MeasureTheory.integral Real Complex Complex.instNormedAddCommGroup
            (@NormedSpace.complexToReal Complex
              (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
              (@NormedField.toNormedSpace Complex Complex.instNormedField))
            Real.measurableSpace
            (@MeasureTheory.Measure.restrict Real Real.measurableSpace ν
              (@Set.ofPred Real fun x =>
                @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                  (@abs Real Real.lattice Real.instAddGroup x)))
            fun x =>
            @HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub)
              (Complex.exp
                (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                  (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) ↑x ↑ξ) Complex.I))
              (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))) := by sorry
