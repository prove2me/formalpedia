-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P13_lemma42_logarithm_directional_derivative
-- name    : QAlgorithms.Papers.Independent.Dependency50.P13.lemma42_logarithm_directional_derivative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:17:30.372118+00:00
-- url     : https://prove2.me/theorems/e9b5733c-4303-4d30-95bf-71d783cd7f00
-- title:
--   Lemma 42: directional derivative of the operator logarithm
-- statement:
--   Let H be a nonzero separable complex Hilbert space. Let xi and xi' be positive trace-class operators with trace at most one, and rho a state with finite cross entropy -Tr rho ln xi. Suppose a finite real c bounds below the right-hand lower limit of q(lambda)=[Tr rho ln xi-Tr rho ln((1-lambda)xi+lambda xi')]/lambda. Then the interpolated cross entropy is finite for every 0<=lambda<1, both scalar resolvent integrals below are absolutely convergent, and
--
--   $$ \lim_{\lambda\downarrow0}q(\lambda)=\operatorname{Tr}\rho\Gamma_\xi(\xi-\xi')=1-\operatorname{Tr}\rho\Gamma_\xi(\xi')\ge c, $$
--
--   where Tr rho Gamma_xi(X)=integral_0^infinity Tr[rho(xi+sI)^(-1)X(xi+sI)^(-1)] ds. Cross entropy is represented by the extended nonnegative resolvent integral (A3), so support failures retain infinity. The lower limit is taken in the extended reals and the finite c excludes negative infinity.
--
--   This supplies a scalar directional derivative and its integrability, without assuming a bounded operator-valued derivative on the whole trace class.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, PDF p. 40, Lemma 42: directional derivative of the operator logarithm

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 42, arXiv:2105.08091v3, PDF pp.40–42, (A1),(A2).
Cross-entropy finiteness includes support containment. The liminf uses EReal to avoid
an unbounded real liminf default; c is a finite real number. Absolute convergence of
both specified scalar resolvent integrals is part of the conclusion. -/
theorem lemma42_logarithm_directional_derivative [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    {I : Type*} [Countable I] (b : HilbertBasis I ℂ H)
    (xi xiPrime : TraceClass H) (hxi : IsPositive xi.val) (hxiPrime : IsPositive xiPrime.val)
    (htrace : (operatorTrace b xi.val).re ≤ 1)
    (htracePrime : (operatorTrace b xiPrime.val).re ≤ 1) (rho : State b)
    (hfinite : traceCrossEntropy b rho xi.val < ⊤) (c : ℝ)
    (hlower : (c : EReal) ≤ Filter.liminf
      (fun lam : ℝ => (logDifferenceQuotient b rho xi.val xiPrime.val lam : EReal))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))) :
    (∀ lam ∈ Set.Ico (0 : ℝ) 1,
      traceCrossEntropy b rho (operatorMixture xi.val xiPrime.val lam) < ⊤) ∧
    MeasureTheory.IntegrableOn (traceResolventIntegrand b rho xi.val (xi.val - xiPrime.val))
      (Set.Ioi 0) ∧
    MeasureTheory.IntegrableOn (traceResolventIntegrand b rho xi.val xiPrime.val) (Set.Ioi 0) ∧
    Tendsto (logDifferenceQuotient b rho xi.val xiPrime.val)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
      (nhds (traceGamma b rho xi.val (xi.val - xiPrime.val))) ∧
    traceGamma b rho xi.val (xi.val - xiPrime.val) = 1 - traceGamma b rho xi.val xiPrime.val ∧
    c ≤ traceGamma b rho xi.val (xi.val - xiPrime.val) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P13

end
