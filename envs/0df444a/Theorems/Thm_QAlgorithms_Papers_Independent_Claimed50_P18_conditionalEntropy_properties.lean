-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_conditionalEntropy_properties
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.conditionalEntropy_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:00:17.313823+00:00
-- url     : https://prove2.me/theorems/00757173-9c6e-4e12-a95b-b175d27bd1b5
-- title:
--   Conditional entropy: monotonicity, concavity and subadditivity
-- statement:
--   Let $A,B,C,D$ be arbitrary separable complex quantum systems. States are normalized positive trace-class operators, all marginals below come from the same joint state, and entropy uses natural logarithms. On the domain $H(A)<\infty$, define $H(A|B)=H(A)-D(\rho_{AB}\Vert\rho_A\otimes\rho_B)$. Then:
--
--   1. For every state $\rho_{ABC}$ with $H(A)<\infty$,
--   $$H(A|BC)\le H(A|B).$$
--   2. If $\rho_{AB}=\alpha\rho^1_{AB}+(1-\alpha)\rho^2_{AB}$, where $\alpha\in[0,1]$ and both component $A$ marginal entropies are finite, then
--   $$H(A|B)_\rho\ge\alpha H(A|B)_{\rho_1}+(1-\alpha)H(A|B)_{\rho_2}.$$
--   3. For every state $\rho_{ABCD}$ with $H(A),H(B)<\infty$,
--   $$H(AB|CD)\le H(A|C)+H(B|D).$$
--
--   These are the three structural properties of the finite-first-entropy extension. No entropy bound is required on a conditioning system.
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 3, §2, Proposition 1, all three clauses: monotonicity, concavity and subadditivity (7)–(9)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

/-- Proposition 1, all three clauses (7)–(9), PDF pp.3–7.
Both components of a mixture belong to the finite-first-entropy domain, including
at weights zero and one. Finiteness of H(AB) in clause three is a consequence. -/
theorem conditionalEntropy_properties (A B C D : Type)
    [Countable A] [Countable B] [Countable C] [Countable D] :
    (∀ rho : State (A × (B × C)),
      homogeneousEntropy (traceSecond rho.coefficients) < ⊤ →
      finiteFirstConditionalEntropy rho.coefficients ≤
        finiteFirstConditionalEntropy (traceSecond (associateLeft rho.coefficients))) ∧
    (∀ (rho rho1 rho2 : State (A × B)) (alpha : ℝ),
      alpha ∈ Set.Icc 0 1 →
      homogeneousEntropy (traceSecond rho1.coefficients) < ⊤ →
      homogeneousEntropy (traceSecond rho2.coefficients) < ⊤ →
      rho.coefficients = convexOperatorMixture alpha rho1.coefficients rho2.coefficients →
      (alpha : EReal) * finiteFirstConditionalEntropy rho1.coefficients +
        ((1-alpha : ℝ) : EReal) * finiteFirstConditionalEntropy rho2.coefficients ≤
          finiteFirstConditionalEntropy rho.coefficients) ∧
    (∀ rho : State ((A × B) × (C × D)),
      homogeneousEntropy (traceSecond (traceSecond rho.coefficients)) < ⊤ →
      homogeneousEntropy (traceFirst (traceSecond rho.coefficients)) < ⊤ →
      finiteFirstConditionalEntropy rho.coefficients ≤
        finiteFirstConditionalEntropy
          (traceSecond (associateLeft (dropMiddle (associateRight rho.coefficients)))) +
          finiteFirstConditionalEntropy (marginalBD rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
