-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_london_collisionFrequency
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.london_collisionFrequency
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:29:25.364635+00:00
-- url     : https://prove2.me/theorems/b5e89985-a7d7-4f2a-a079-ffd8abe5e252
-- title:
--   §7.2.2: London-law collision frequency and small-velocity expansion, (7.20), (7.22)–(7.24)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   Assume $C_6>0$ and the stated semiclassical London cross-section $\sigma_{\rm tot}(w)=\pi^2[\sin(\pi/5)\Gamma(2/5)]^{-1}(3\pi C_6/(8\hbar))^{2/5}w^{-2/5}$. Put $u=|P|/(Mv_\beta)$ and $A=n_{\rm gas}\frac{4\pi\Gamma(9/10)}{5\sin(\pi/5)}(3\pi C_6/(2\hbar))^{2/5}v_\beta^{3/5}$. Its thermal collision rate is
--   $$
--   \Gamma_{\rm tot}(P)=A\,{}_1F_1\left(-\frac3{10};\frac32;-u^2\right)=A\left[1+\frac{u^2}{5}+O(u^4)\right].
--   $$
--   The identity includes $P=0$; for each fixed model and beam direction there are positive constants $C,\delta$, before $u$, bounding the bracket remainder by $Cu^4$ on $0\le u\le\delta$. This evaluates the prescribed semiclassical model rather than deriving exact scattering from a singular potential.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 38, §7.2.2: London-law collision frequency and small-velocity expansion, (7.20), (7.22)–(7.24)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass State relativeEntropy traceNormTopology)

open QAlgorithms.Papers.Independent.Next46.P09 (IsTraceLinear IsTraceCP)

/-- PDF pp.37–38, (7.20),(7.22)–(7.24): exact London-law rate, including
zero speed, and an O(u^4) expansion with constants uniform over u near zero.
The hypergeometric first parameter is negative -3/10. -/
theorem london_collisionFrequency (a : GasTracerParameters) (beta C6 : ℝ)
    (hbeta : 0 < beta) (hC6 : 0 < C6) :
    (∀ P, londonRate a beta C6 P = londonBaseRate a beta C6 *
      kummer (-3 / 10) (3 / 2) (-((‖P‖ / (a.M * thermalSpeed a beta)) ^ 2))) ∧
    (∀ axis : Momentum, ‖axis‖ = 1 → ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ delta →
        |londonRate a beta C6 ((a.M * thermalSpeed a beta * u) • axis) /
          londonBaseRate a beta C6 - (1 + u ^ 2 / 5)| ≤ C * u ^ 4) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
