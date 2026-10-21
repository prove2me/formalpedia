-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_freeParticle_nonzeroLimit
-- name    : QAlgorithms.Papers.Independent.Next46.P31.freeParticle_nonzeroLimit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:32:21.75763+00:00
-- url     : https://prove2.me/theorems/ad8e1ace-3153-4587-ab00-4c000d6a5cbc
-- title:
--   Unnumbered introduction result: free evolution has nonvanishing limiting spatial coherence
-- statement:
--   Let $d\ge1$, let $H=L^2(\mathbb R^d,dx)$, and let $\rho$ be a positive trace-class operator on $H$ with trace one. Assume that $X_j\rho$ and $K_j\rho$ have trace-class bounded realizations for every canonical position and momentum coordinate. Products with unbounded coordinates are interpreted through their forms on the dense operator domains. Write $C_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|[A_j,\rho]\|_2^2)^{1/2}$, $D_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|\{A_j-\operatorname{Tr}(A_j\rho),\rho\}\|_2^2)^{1/2}$, and $S_A=C_A/D_A$ on the nonzero-spread domain; $\|\cdot\|_2$ is the Hilbert–Schmidt norm. Let $\Gamma_t$ be free evolution with no Gaussian or jump noise, specified in the characteristic representation by $\varphi_{\Gamma_t(T)}(q,p)=\varphi_T(q+tp,p)$. Then
--
--   $$
--   \exists c>0:\quad \lim_{t\to+\infty}S_X(\Gamma_t\rho)=c.
--   $$
--
--   This asserts the nonvanishing limiting coherence claimed in the introduction, without identifying the constant or adding a rate.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 4, Unnumbered introduction result: free evolution has nonvanishing limiting spatial coherence

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

/-- Clark, PDF p.4, unnumbered free-particle claim. Zero noise uses the same
schrodingerCharacteristic shear; only existence of a strictly positive limit is asserted. -/
theorem freeParticle_nonzeroLimit {I : Type*} {d : ℕ} (hd : 0 < d)
    (b : HilbertBasis I ℂ (EuclideanSchrodinger d))
    (Gamma : ℝ → (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d) → (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d)) (hGamma : CharacteristicDynamics b 0 0 Gamma)
    (rho : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d)) (hrho : IsTraceClass rho ∧ IsPositive rho ∧ operatorTrace b rho = 1) (hregular : CanonicallyRegular rho) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun t : ℝ => coherenceIndex b positionGraph (Gamma t rho))
      atTop (nhds c) := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
