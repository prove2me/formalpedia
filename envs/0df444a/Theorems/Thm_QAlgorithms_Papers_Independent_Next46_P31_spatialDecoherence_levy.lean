-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_spatialDecoherence_levy
-- name    : QAlgorithms.Papers.Independent.Next46.P31.spatialDecoherence_levy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:23:23.409038+00:00
-- url     : https://prove2.me/theorems/1ec114bc-cacf-4b68-8018-0d9536116cd9
-- title:
--   Theorem 4.3, cases 1 and 3: leading spatial decoherence rates (seed from abstract)
-- statement:
--   Let $d\ge1$, let $H=L^2(\mathbb R^d,dx)$, and let $\rho$ be a positive trace-class operator on $H$ with trace one. Assume that $X_j\rho$ and $K_j\rho$ have trace-class bounded realizations for every canonical position and momentum coordinate. Products with unbounded coordinates are interpreted through their forms on the dense operator domains. Write $C_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|[A_j,\rho]\|_2^2)^{1/2}$, $D_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|\{A_j-\operatorname{Tr}(A_j\rho),\rho\}\|_2^2)^{1/2}$, and $S_A=C_A/D_A$ on the nonzero-spread domain; $\|\cdot\|_2$ is the Hilbert–Schmidt norm. Let $A$ be a real symmetric positive-semidefinite matrix in $(q,p)$ block order and let $\mu$ be a positive origin-symmetric Borel Lévy measure, with zero mass at the origin and $\int(|x|^2+|k|^2)\,d\mu(x,k)<\infty$; its total mass may be infinite. Let $\Gamma_t$ be the characteristic dynamics defined by $\varphi_T(q,p)=\operatorname{Tr}(W_{q,p}T)$ and
--
--   $$
--   \varphi_{\Gamma_t(T)}(q,p)=\exp\!\left(\int_0^t\left[-\tfrac12\langle(q+(t-s)p,p),A(q+(t-s)p,p)\rangle+\psi_\mu(q+(t-s)p,p)\right]ds\right)\varphi_T(q+tp,p),
--   $$
--
--   where $W_{q,p}f(x)=e^{ip\cdot(x-q/2)}f(x-q)$ and $\psi_\mu(q,p)=\int(\cos(q\cdot k+p\cdot x)-1)\,d\mu(x,k)$. Either (1) $A_{xk}=A_{kx}=A_{kk}=0$ and $\mu=\delta_0(dx)\nu(dk)$, where $A_{xx}$ is positive definite or $\nu$ is nonzero and absolutely continuous; or (3) $A$ is positive definite or $\mu$ is nonzero and absolutely continuous. Put $M=\int k\otimes k\,d\mu(x,k)$ and $D=A_{xx}+M$. Then, as $t\to+\infty$,
--
--   $$
--   S_X(\Gamma_t\rho)\sim\sqrt3\,\frac{\sqrt{\operatorname{Tr}(D^{-1})}}{\sqrt{\operatorname{Tr}D}}\,t^{-2}.
--   $$
--
--   The equivalence includes the leading constant and covers both indicated noise regimes. It gives no asserted remainder estimate.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 18, Theorem 4.3, cases 1 and 3: leading spatial decoherence rates (seed from abstract)

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

/-- Clark, PDF pp.18–20, Theorem 4.3(1),(3), with (1.3),(1.5) on p.2.
Printed: the moment hypothesis uses dnu(x,k), the B block labels use (x,k)
order, and the density alternatives do not explicitly exclude zero measures.
Changed: integrate against mu, use integral k tensor k dmu for the q,q noise
covariance, and require a nonzero measure in each absolute-continuity alternative.
Why: (1.20) pairs q with k, the p.19 proof uses that covariance, and the proof's
positive covariance excludes the zero-density case. At A=0, mu=0 the printed
rate degenerates, whereas free evolution has nonvanishing coherence.
No expected remainder term is asserted. -/
theorem spatialDecoherence_levy {I : Type*} {d : ℕ} (hd : 0 < d)
    (b : HilbertBasis I ℂ (EuclideanSchrodinger d))
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (mu : Measure (PhasePoint d))
    (hnoise : FiniteVarianceLevyNoise A mu) (Gamma : ℝ → (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d) → (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d))
    (hGamma : CharacteristicDynamics b A mu Gamma)
    (rho : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d)) (hrho : IsTraceClass rho ∧ IsPositive rho ∧ operatorTrace b rho = 1) (hregular : CanonicallyRegular rho)
    (hregime : MomentumNoiseRegime A mu ∨ FullNoiseRegime A mu) :
    Tendsto (fun t : ℝ => coherenceIndex b positionGraph (Gamma t rho) /
      (leadingCoefficient (positionBlock A + momentumMoment mu) / t ^ 2))
      atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
