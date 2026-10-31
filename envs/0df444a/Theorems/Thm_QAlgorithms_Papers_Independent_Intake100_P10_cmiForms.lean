-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_cmiForms
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.cmiForms
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:06:09.025201+00:00
-- url     : https://prove2.me/theorems/18b350d8-be28-4f26-977f-5c0343ed1720
-- title:
--   No-signaling removes input CMI and gives both alternate forms
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. For every instrument $\{\mathcal K_y\}_y$, every input channel $p(x\mid y)$, and every extension in (11)–(13), let $\omega$ be the cq state with blocks $p(x\mid y)\hat\rho_{B'E}^{a,x,y}$ and classical labels $x,a,y$. Then $I(X;B'\mid EY)_\omega=0$ and $I(XA;B'\mid EY)_\omega=I(A;B'\mid EXY)_\omega$. For every input law $p(x)$ and every extension in (16)–(17), the corresponding state $\eta$ has $I(X;B\mid E)_\eta=0$ and $I(XA;B\mid E)_\eta=I(A;B\mid EX)_\eta$. Consequently the optimized forms are
--
--   $$S(\hat\rho)=\sup_{p(x\mid y),\{\mathcal K_y\}}\inf_{\omega}I(A;B'\mid EXY)_\omega,$$
--   $$S^R(\hat\rho)=\sup_{p(x)}\inf_{\eta}I(A;B\mid EX)_\eta.$$
--
--   All quantities use binary logarithms and actual register permutations. Vanishing input CMI is a conclusion of the admissibility constraints, including at zero-probability inputs.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 3, Equations (15) and (19)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P10

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (PositiveTraceClass operatorTrace partialTraceFirst partialTraceSecond IsQuantumOperation)

open QAlgorithms.Papers.Independent.Renew46.P08 (qcmi)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

/-- Unnumbered structural identities before (15),(19), PDF pp.3--4. Both
vanishing input CMIs and both alternative optimized formulas are conclusions,
never hypotheses. CQ register permutations are explicit coefficient embeddings. -/
theorem cmiForms {X A B : Type} [Fintype X] [Fintype A] [Nonempty X] [Nonempty A]
    (rho : AssemblageCoefficients X A B) (hrho : IsAssemblage rho) :
    (∀ (Bf Y : Type) (K : DiscreteTraceClassInstrument B Bf Y) (p : Y → PMF X)
      (E : Type) (r : ProcessedExtension rho K E),
      cmiBits (processedInputCoefficients p r.block) = 0 ∧
        cmiBits (processedCoefficients p r.block) = cmiBits (processedOutcomeCoefficients p r.block)) ∧
    (∀ (p : PMF X) (E : Type) (r : Extension rho E),
      cmiBits (inputCoefficients p r.block) = 0 ∧
        cmiBits (cqCoefficients p r.block) = cmiBits (outcomeCoefficients p r.block)) ∧
    (intrinsicSteerability rho =
      ⨆ (Bf : Type) (Y : Type) (K : DiscreteTraceClassInstrument B Bf Y) (p : Y → PMF X),
        ⨅ (E : Type) (r : ProcessedExtension rho K E),
          cmiBits (processedOutcomeCoefficients p r.block)) ∧
    (restrictedSteerability rho =
      ⨆ p : PMF X, ⨅ (E : Type) (r : Extension rho E), cmiBits (outcomeCoefficients p r.block)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
