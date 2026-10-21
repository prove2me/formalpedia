-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_schmidtWitness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.schmidtWitness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:48:43.511422+00:00
-- url     : https://prove2.me/theorems/86b1ad4e-9bc3-4c77-8266-aa060274e397
-- title:
--   Unnumbered: existence of a k-Schmidt witness
-- statement:
--   Let $H,K$ be separable complex Hilbert spaces, $k\ge1$, and $\rho_0\in S_k\setminus S_{k-1}$, with $S_0=\varnothing$. There is a bounded Hermitian operator $W$ on $H\otimes K$ such that
--
--   $$\operatorname{Tr}(W\rho)\ge0\quad(\rho\in S_{k-1}),\qquad\operatorname{Tr}(W\rho_0)<0.$$
--
--   Such an operator is a $k$-Schmidt witness detecting $\rho_0$. At $k=1$ the first condition tests the empty set and $W=-I$ is allowed.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 9, Unnumbered: existence of a k-Schmidt witness

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

/-- arXiv:1110.4363v3, PDF p.9, unnumbered Hahn–Banach witness existence.
At k=1 the tested class is empty, and the negative identity is admissible. -/
theorem schmidtWitness {I J : Type} [Countable I] [Countable J]
    (k : ℕ) (hk : 0 < k) (rho : State (I × J))
    (hrho : rho ∈ schmidtClass I J k \ schmidtClass I J (k - 1)) :
    ∃ W : BoundedOp (I × J) (I × J), witness k rho W := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
