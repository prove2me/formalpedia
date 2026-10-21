-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition9B
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition9B
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:53:53.427985+00:00
-- url     : https://prove2.me/theorems/8e3dc930-c011-479b-947a-f3f05756943d
-- title:
--   Proposition 9B: exact k-PEB channels with only infinite-rank nonzero Kraus operators
-- statement:
--   Let $H,H'$ be infinite-dimensional separable complex Hilbert spaces and $k\ge1$. There exists a channel
--
--   $$\Phi\in\mathcal P_k(H,H')\setminus\mathcal P_{k-1}(H,H')$$
--
--   such that every nonzero operator in every countable Kraus representation of $\Phi$ has infinite rank. Here $\mathcal P_0=\varnothing$. A Kraus representation has strongly convergent $\sum_iV_i^*V_i=I$ and trace-norm convergence of $\sum_iV_iXV_i^*$ on trace-class inputs.
--
--   The nonzero-entry convention corrects the printed statement: appending a zero operator cannot change the channel. This result separates mixed Schmidt classes from countable bounded-rank Kraus descriptions.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 12, Proposition 9B: exact k-PEB channels with only infinite-rank nonzero Kraus operators

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

/-- arXiv:1110.4363v3, PDF pp.12–13, Proposition 9B (title-node target).
Printed: every Kraus entry has infinite rank. Changed: every NONZERO entry,
because appending a zero operator preserves the representation. P_0 is empty. -/
theorem proposition9B {I J : Type} [Countable I] [Countable J] [Infinite I] [Infinite J]
    (k : ℕ) (hk : 0 < k) :
    ∃ Phi : CanonicalChannel I J, isPEB k Phi ∧ ¬ isPEB (k - 1) Phi ∧
      ∀ V : ℕ → BoundedOp I J, krausRepresentation Phi V →
        ∀ i, V i ≠ 0 → ∀ r : ℕ, ¬ arrayRankLE r (opCoeff (V i)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
