-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_extendedRelativeEntropy_monotone_of_finite_ssa
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.extendedRelativeEntropy_monotone_of_finite_ssa
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T00:31:26.733792+00:00
-- url     : https://prove2.me/theorems/0cad31e2-2569-4406-81d8-28c6b3e20b18
-- title:
--   Monotonicity of the extended relative entropy under channels, from finite-dimensional monotonicity
-- statement:
--   Assume monotonicity of the relative entropy under partial traces for invertible finite-dimensional density matrices. Then for every channel $\Phi$ and density operators $X,Y$ on a countable register,
--
--   $$D(\Phi(X)\,\|\,\Phi(Y))\le D(X\,\|\,Y)$$
--
--   for the extended (Lindblad) relative entropy.
--
--   Role: Gives both inequalities in the equality-of-entropies direction of the parent (applied to $\Phi$ and to the reversing channel); the hypothesis is the existing Proved theorem SimpleSSA.Monotone.eq_4.
-- source:
--   G. Lindblad, Completely positive maps and entropy inequalities, Comm. Math. Phys. 40 (1975) 147-151, main theorem; used as monotonicity in M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, Sec. 2 (Theorem 1 proof, PDF pp. 6-7)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
import Definitions.Def_SimpleSSA_Monotone_Basic

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

open scoped ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)

theorem extendedRelativeEntropy_monotone_of_finite_ssa
    (h4 : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (ρ σ : Matrix (A × B) (A × B) ℂ), QAlgorithms.IsDensityMatrix ρ → ρ.PosDef →
      QAlgorithms.IsDensityMatrix σ → σ.PosDef →
      SimpleSSA.Monotone.relEntropy (WildeQIT.partialTraceRight ρ) (WildeQIT.partialTraceRight σ) ≤
        SimpleSSA.Monotone.relEntropy ρ σ)
    {I J : Type} [Countable I] [Nonempty I] (Phi : Channel I J)
    (X Y : Matrix I I ℂ) (hX : QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity X)
    (hY : QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity Y) :
    extendedRelativeEntropyNats (Phi.val X) (Phi.val Y) ≤ extendedRelativeEntropyNats X Y := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
