-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition6
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:49:33.086818+00:00
-- url     : https://prove2.me/theorems/d155360a-0afe-416b-95e5-386682ce721a
-- title:
--   Proposition 6: finite-rank edge-state witness construction
-- statement:
--   Let $H,K$ be infinite-dimensional separable complex Hilbert spaces and $k\ge2$. Let $\delta$ be a finite-operator-rank density state with Schmidt number at least $k$ such that $\delta-\lambda\sigma$ is not positive for any $\lambda>0$ and $\sigma\in S_{k-1}$. Let $P,C$ be bounded positive operators with $\operatorname{ran}P=\ker\delta$, $\operatorname{Tr}(C\delta)>0$, and $P$ bounded below by a positive constant on $\ker\delta$. Define
--
--   $$\epsilon=\inf_{\sigma\in S_{k-1}^p}\operatorname{Tr}(P\sigma),\qquad c=\|C\|,\qquad W=P-\frac{\epsilon}{c}C.$$
--
--   Then $\epsilon>0$, $c>0$, and $W$ is a $k$-Schmidt witness detecting $\delta$. Here $S_{k-1}^p$ denotes normalized pure states of Schmidt rank at most $k-1$.
--
--   The lower bound on the kernel is the proof-compatible correction of the printed, impossible global spectral invertibility condition.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 9, Proposition 6: finite-rank edge-state witness construction

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

/-- arXiv:1110.4363v3, PDF pp.9–10, Proposition 6 and its displayed formula.
Printed: zero not in the spectrum of P on the entire space. Changed: P has a
positive lower bound on ker(delta). Global invertibility contradicts ran(P)=ker(delta)
for a nonzero density. The proof's projection onto ker(delta) meets this corrected
condition. Arbitrary P and C are retained; independent moderation must check it. -/
theorem proposition6 {I J : Type} [Countable I] [Countable J] [Infinite I] [Infinite J]
    (k : ℕ) (hk : 2 ≤ k) (delta : State (I × J)) (hedge : edgeState k delta)
    (hfinite : ∃ n, arrayRankLE n delta.coefficients)
    (P C : BoundedOp (I × J) (I × J))
    (hP : P.adjoint = P ∧ ∀ v, 0 ≤ (inner ℂ v (P v)).re)
    (hC : C.adjoint = C ∧ ∀ v, 0 ≤ (inner ℂ v (C v)).re)
    (hrange : ∀ v, inKernel delta.coefficients v ↔ ∃ u, P u = v)
    (hgap : ∃ a : ℝ, 0 < a ∧ ∀ v, inKernel delta.coefficients v →
      a * ‖v‖ ^ 2 ≤ (inner ℂ v (P v)).re)
    (htrace : 0 < tracePair C delta.coefficients) :
    let e := sInf {t : ℝ | ∃ sigma : PureState (I × J),
      schmidtRank sigma ≤ ((k - 1 : ℕ) : ℝ≥0∞) ∧ t = tracePair P sigma.val.coefficients}
    0 < e ∧ 0 < ‖C‖ ∧ witness k delta (P - ((e / ‖C‖ : ℝ) : ℂ) • C) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
