-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_characteristic_firstDerivative
-- name    : QAlgorithms.Papers.Independent.Next46.P31.characteristic_firstDerivative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:29:05.089985+00:00
-- url     : https://prove2.me/theorems/15a567f5-4c3c-443a-9691-f5cfaf0cd773
-- title:
--   Lemma A.2, first assertion: characteristic-function C¹ regularity
-- statement:
--   Let $d\ge1$, let $H=L^2(\mathbb R^d,dx)$, and let $\rho$ be a positive trace-class operator on $H$ with trace one. Assume that $X_j\rho$ and $K_j\rho$ have trace-class bounded realizations for every canonical position and momentum coordinate. Products with unbounded coordinates are interpreted through their forms on the dense operator domains. For the actual Schrödinger Weyl operators $W_{q,p}f(x)=e^{ip\cdot(x-q/2)}f(x-q)$, define $\varphi_\rho(q,p)=\operatorname{Tr}(W_{q,p}\rho)$. Then
--
--   $$
--   \varphi_\rho\in C^1(\mathbb R^{2d};\mathbb C),\qquad \sup_{(q,p)\in\mathbb R^{2d}}\|D\varphi_\rho(q,p)\|<\infty.
--   $$
--
--   This is exactly the bounded continuous first-derivative assertion. The separate printed directional identity is deferred.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 22, Lemma A.2, first assertion: characteristic-function C¹ regularity

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Next46.P31

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace)

/-- Clark, PDF p.22, Lemma A.2, first assertion only. Boundedness is of the
entire real derivative, equivalent in finite dimension to bounded first partials. -/
theorem characteristic_firstDerivative {I : Type*} {d : ℕ} (hd : 0 < d)
    (b : HilbertBasis I ℂ (EuclideanSchrodinger d)) (rho : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d))
    (hrho : IsTraceClass rho ∧ IsPositive rho ∧ operatorTrace b rho = 1) (hregular : CanonicallyRegular rho) :
    ContDiff ℝ 1 (schrodingerCharacteristic b rho) ∧
      Bornology.IsBounded (Set.range (fderiv ℝ (schrodingerCharacteristic b rho))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
