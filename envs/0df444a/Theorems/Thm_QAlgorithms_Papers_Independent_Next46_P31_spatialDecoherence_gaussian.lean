-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_spatialDecoherence_gaussian
-- name    : QAlgorithms.Papers.Independent.Next46.P31.spatialDecoherence_gaussian
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:24:13.923516+00:00
-- url     : https://prove2.me/theorems/eb3278c2-24b8-42ad-9ef2-8cd137e1a6c6
-- title:
--   Proposition 4.1, cases 1 and 3: Gaussian-noise rates
-- statement:
--   Let $d\ge1$, let $H=L^2(\mathbb R^d,dx)$, and let $\rho$ be a positive trace-class operator on $H$ with trace one. Assume that $X_j\rho$ and $K_j\rho$ have trace-class bounded realizations for every canonical position and momentum coordinate. Products with unbounded coordinates are interpreted through their forms on the dense operator domains. Write $C_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|[A_j,\rho]\|_2^2)^{1/2}$, $D_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|\{A_j-\operatorname{Tr}(A_j\rho),\rho\}\|_2^2)^{1/2}$, and $S_A=C_A/D_A$ on the nonzero-spread domain; $\|\cdot\|_2$ is the Hilbert–Schmidt norm. Assume the characteristic evolution above has zero jump measure and Gaussian covariance $A\succeq0$. Suppose either $A_{xk}=A_{kx}=A_{kk}=0$ and $A_{xx}$ is positive definite, or the whole matrix $A$ is positive definite. For the dynamics specified by the shear $q+tp$ in (1.19),
--
--   $$
--   S_X(\Gamma_t\rho)\sim\sqrt3\,\frac{\sqrt{\operatorname{Tr}(A_{xx}^{-1})}}{\sqrt{\operatorname{Tr}A_{xx}}}\,t^{-2}\qquad(t\to+\infty).
--   $$
--
--   This gives both Gaussian cases 1 and 3 with their exact leading constant.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 15, Proposition 4.1, cases 1 and 3: Gaussian-noise rates

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

/-- Clark, PDF pp.15–17, Proposition 4.1(1),(3): Gaussian special cases.
Positive means positive definite, as used in the proof's inverse/diagonalization. -/
theorem spatialDecoherence_gaussian {I : Type*} {d : ℕ} (hd : 0 < d)
    (b : HilbertBasis I ℂ (EuclideanSchrodinger d))
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (hA : A.PosSemidef)
    (Gamma : ℝ → (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d) → (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d))
    (hGamma : CharacteristicDynamics b A 0 Gamma)
    (rho : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d)) (hrho : IsTraceClass rho ∧ IsPositive rho ∧ operatorTrace b rho = 1) (hregular : CanonicallyRegular rho)
    (hregime : (OnlyMomentumGaussian A ∧ (positionBlock A).PosDef) ∨ A.PosDef) :
    Tendsto (fun t : ℝ => coherenceIndex b positionGraph (Gamma t rho) /
      (leadingCoefficient (positionBlock A) / t ^ 2)) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
