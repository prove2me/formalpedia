-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_thermalStationarityAndLocalMinimum
-- name    : QAlgorithms.Papers.Independent.Next46.P27.thermalStationarityAndLocalMinimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:20:46.735412+00:00
-- url     : https://prove2.me/theorems/4136e0c4-678c-4bc8-b275-7962784a6f85
-- title:
--   Thermal and displaced thermal stationary witnesses and local output-entropy minima
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N;\mathbb C)$ be the full single-mode Fock space and let $\Phi_v$ be the Gaussian displacement channel of Eq.(1), with density $e^{-|\mu|^2/v}/(\pi v)$ relative to complex-plane area. Densities are positive normalized trace-class operators; entropy $S$ is in nats and may be infinite.
--
--   For every $\beta>0$, $v>0$, and $a\in\mathbb C$, set $\rho=D(a)\rho_\beta D(a)^\dagger$, where $\rho_\beta=(1-e^{-\beta})\sum_{j\ge0}e^{-\beta j}|j\rangle\langle j|$, and set $z=\Phi_v(\rho)$. These are densities and $0<S(\rho)<\infty$. Write $Q_X$ for the extended spectral form of $-\log X$ and $\mathcal D=\{u:\sum_j j|u_j|^2<\infty\}$. There exist real $\lambda,\alpha,\eta,c$ and a closed densely defined nonnegative Hermitian form $L$ such that $Q_\rho,Q_z,L,\Phi_v^*L$ are closed forms with finite domain exactly $\mathcal D$. The actual Gaussian pullback integrand is almost everywhere strongly measurable, and for every $u\in\mathcal D$,
--
--   $$Q_z(u)-(1+\eta)\|u\|^2-L(u)+c\|u\|^2=0,$$
--   $$ (\lambda+1)(\|u\|^2-Q_\rho(u))-\alpha\|u\|^2+(\Phi_v^*L)(u)-c\|u\|^2=0.$$
--
--   Here $L-cI$ is the Hermitian multiplier in Eq.(8). Independently, there exists $r>0$ such that every density $X$ with $S(X)=S(\rho)$ and $\|X-\rho\|_1<r$ satisfies
--
--   $$S(\Phi_v(\rho))\le S(\Phi_v(X)).$$
--
--   Thus every thermal displacement has both stationary witnesses and constrained local minimality. No uniqueness or global output-entropy minimum is asserted.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 1, Unnumbered main result: thermal stationarity and local output-entropy minima

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF pp.1,3–4: thermal and displaced thermal stationary witnesses and
constrained local minima. Eq.(8) is interpreted on the full common closed form
domain. Every complex displacement is included, as stated after Eq.(8).
Local minimality is a separate conclusion, not a definition of stationarity. -/
theorem thermalStationarityAndLocalMinimum (beta v : ℝ) (hbeta : 0 < beta) (hv : 0 < v) :
    ∀ displacementAlpha : ℂ, ThermalStationary beta v displacementAlpha ∧
      LocalOutputMinimum v (A.conjugateBy (B.displacement displacementAlpha)
        (A.photonMeanThermalState (gibbsMean beta))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
