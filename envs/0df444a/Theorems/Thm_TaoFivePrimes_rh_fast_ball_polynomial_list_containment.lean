-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_ball_polynomial_list_containment
-- name    : TaoFivePrimes.rh_fast_ball_polynomial_list_containment
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:30:55.281452+00:00
-- url     : https://prove2.me/theorems/3dde08ca-3c11-48eb-9c34-ea1dda74527e
-- title:
--   TaoFivePrimes.rh_fast_ball_polynomial_list_containment
-- statement:
--   Integer ball polynomial addition, convolution and positive integer division preserve coefficientwise containment.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallPolynomialArithmetic
import Definitions.Def_TaoFivePrimes_RHFastComplexPolynomialLists
import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
open Complex

theorem TaoFivePrimes.rh_fast_ball_polynomial_list_containment (D:Nat) (hD:0<D) :
 (∀(xs:List RHFastBallArithmetic.Ball)(us:List ℂ)(ys:List RHFastBallArithmetic.Ball)(vs:List ℂ),
  List.Forall₂ (RHFastBallSemantics.encloses D) xs us → List.Forall₂ (RHFastBallSemantics.encloses D) ys vs →
  List.Forall₂ (RHFastBallSemantics.encloses D) (RHFastBallPoly.addList xs ys) (RHFastComplexPoly.addList us vs)) ∧
 (∀(xs:List RHFastBallArithmetic.Ball)(us:List ℂ)(ys:List RHFastBallArithmetic.Ball)(vs:List ℂ),
  List.Forall₂ (RHFastBallSemantics.encloses D) xs us → List.Forall₂ (RHFastBallSemantics.encloses D) ys vs →
  List.Forall₂ (RHFastBallSemantics.encloses D) (RHFastBallPoly.mulList D xs ys) (RHFastComplexPoly.mulList us vs)) ∧
 (∀(xs:List RHFastBallArithmetic.Ball)(us:List ℂ)(n:Nat),0<n →
  List.Forall₂ (RHFastBallSemantics.encloses D) xs us →
  List.Forall₂ (RHFastBallSemantics.encloses D) (RHFastBallPoly.divideList xs n) (RHFastComplexPoly.divideList us n)) := by sorry
