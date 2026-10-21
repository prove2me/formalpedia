-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_conditionalEntropy_bounds
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.conditionalEntropy_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:02:33.844985+00:00
-- url     : https://prove2.me/theorems/4fe67fbd-ebbc-4f30-b524-9cac5b2b82ea
-- title:
--   Conditional entropy is bounded by first-marginal entropy
-- statement:
--   For a pure normalized trace-class state rho_ABC on separable complex systems with H(C)<infinity, the two conditional entropies are finite and satisfy
--   $$-H(C)\le H(C|A)\le H(C),\qquad -H(C)\le H(C|B)\le H(C).$$
--   Equivalently, their absolute values are at most H(C). For every bipartite state rho_AC with finite H(C), the same bound holds for H(C|A), without a purity assumption on rho_AC.
--
--   This gives finite values for the extended relative-entropy definition even when the conditioning marginal entropy is infinite. The inequalities are stated in signed extended reals, so finiteness is a conclusion.
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 2, §1, unnumbered boundedness result (5)

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

/-- Both purification bounds (5), and their arbitrary-bipartite reading, PDF p.2.
The extended inequalities themselves establish finiteness. -/
theorem conditionalEntropy_bounds (A B C : Type) [Countable A] [Countable B] [Countable C] :
    (∀ rho : PureState ((A × B) × C),
      homogeneousEntropy (traceFirst rho.val.coefficients) < ⊤ →
      let hc := (homogeneousEntropy (traceFirst rho.val.coefficients) : EReal);
      let ca := finiteFirstConditionalEntropy (swapCoeff (dropMiddle (associateRight rho.val.coefficients)));
      let cb := finiteFirstConditionalEntropy (swapCoeff (traceFirst (associateRight rho.val.coefficients)));
      (-hc ≤ ca ∧ ca ≤ hc) ∧ (-hc ≤ cb ∧ cb ≤ hc)) ∧
    (∀ rho : State (A × C), homogeneousEntropy (traceFirst rho.coefficients) < ⊤ →
      let hc := (homogeneousEntropy (traceFirst rho.coefficients) : EReal);
      -hc ≤ finiteFirstConditionalEntropy (swapCoeff rho.coefficients) ∧
        finiteFirstConditionalEntropy (swapCoeff rho.coefficients) ≤ hc) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
