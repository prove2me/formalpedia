-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P24_symmetryReduction
-- name    : QAlgorithms.Papers.Independent.Support50.P24.symmetryReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:58:10.016548+00:00
-- url     : https://prove2.me/theorems/de6a329e-0bb4-4511-91d5-8fecc0a6bea2
-- title:
--   Objective-preserving Haar symmetry reduction
-- statement:
--   Let $d\ge1$, $n\ge0$, and let $C$ be the Choi matrix of a deterministic sequential $n$-slot comb, or of a parallel strategy for $U^{\otimes n}$. Choi matrices use the unnormalized, input-first convention. Group the wires as $(I_1,\ldots,I_n,F)$ and $(P,O_1,\ldots,O_n)$. Let $\Omega$ be the actual inversion performance operator in (S77), with normalized Haar measure and the factor $1/d^2$. Define $R(V,W)=V^{\otimes(n+1)}\otimes W^{\otimes(n+1)}$ and
--
--   $$\overline C=\int R(V,W)C R(V,W)^\dagger\,dV\,dW.$$
--
--   The defining matrix integrals and scalar objective integrand are integrable. The matrix $\overline C$ satisfies the same class of comb constraints, both $\Omega$ and $\overline C$ commute with every $R(V,W)$, and
--
--   $$\operatorname{Tr}(\overline C\Omega)=\operatorname{Tr}(C\Omega)\in\mathbb R.$$
--
--   Thus imposing the symmetry preserves every attainable objective and every optimum.
-- source:
--   Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly, arXiv:2209.02907v5, PDF p. 3, Unnumbered main result, Eqs.(10)–(11): SU(d)×SU(d) symmetry reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Support50.P24

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P24.groupedContinuousENorm

/-- PDF pp.3,21-22,24: the concrete Haar average is feasible, invariant and
objective preserving for either sequential or parallel combs. All integrability is concluded. -/
theorem symmetryReduction (d n : ℕ) (hd : 0 < d) (parallel : Bool)
    (C : GroupedComb d (n+1))
    (hC : if parallel then ParallelFeasible C else SequentialFeasible d (n+1) C) :
    Integrable (@performanceKernel d n) (QAlgorithms.Papers.Independent.Next46.P24.haar d) ∧
    Integrable (fun U => (C * performanceKernel U).trace.re)
      (QAlgorithms.Papers.Independent.Next46.P24.haar d) ∧
    Integrable (averagingKernel C)
      ((QAlgorithms.Papers.Independent.Next46.P24.haar d).prod
        (QAlgorithms.Papers.Independent.Next46.P24.haar d)) ∧
    (if parallel then ParallelFeasible (averageComb C)
      else SequentialFeasible d (n+1) (averageComb C)) ∧
    (∀ V W : Matrix.specialUnitaryGroup (Fin d) ℂ,
      performanceOperator d n * groupAction V W = groupAction V W * performanceOperator d n ∧
      averageComb C * groupAction V W = groupAction V W * averageComb C) ∧
    (C * performanceOperator d n).trace.im = 0 ∧
    inversionObjective (averageComb C) = inversionObjective C := by sorry

end QAlgorithms.Papers.Independent.Support50.P24

end
