-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_corollary2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.corollary2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:54:40.441715+00:00
-- url     : https://prove2.me/theorems/47d4c002-ca13-4cfc-aa14-bbb8d5304730
-- title:
--   Corollary 2: entanglement-breaking counterexample
-- statement:
--   For any infinite-dimensional separable complex Hilbert input and output spaces there exists an entanglement-breaking channel $\Phi$ such that
--
--   $$V_i\ne0\quad\Longrightarrow\quad\operatorname{rank}V_i=\infty$$
--
--   in every countable Kraus representation $\Phi(X)=\sum_iV_iXV_i^*$. Entanglement breaking is the class $\mathcal P_1$, defined using every separable ancilla and every density input. The series converges in trace norm and $\sum_iV_i^*V_i=I$ strongly.
--
--   Zero Kraus entries are excluded from the rank conclusion because any representation may be padded by them.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 13, Corollary 2: entanglement-breaking counterexample

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- arXiv:1110.4363v3, PDF p.13, Corollary 2. Entanglement breaking is 1-PEB.
The nonzero-entry correction is essential for zero-padded Kraus representations. -/
theorem corollary2 {I J : Type} [Countable I] [Countable J] [Infinite I] [Infinite J] :
    ∃ Phi : CanonicalChannel I J, isPEB 1 Phi ∧
      ∀ V : ℕ → BoundedOp I J, krausRepresentation Phi V →
        ∀ i, V i ≠ 0 → ∀ r : ℕ, ¬ arrayRankLE r (opCoeff (V i)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
