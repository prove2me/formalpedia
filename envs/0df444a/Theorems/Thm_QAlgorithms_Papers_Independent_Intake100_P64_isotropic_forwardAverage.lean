-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_isotropic_forwardAverage
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.isotropic_forwardAverage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:28:17.332051+00:00
-- url     : https://prove2.me/theorems/fcc96d68-8ede-4cae-9c85-9835f5a3b001
-- title:
--   §6.3: Maxwell average of an isotropic forward amplitude, (6.17)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   Let the isotropic forward amplitude be $f(p,p)=g(|p|^2/(2m_*))$, and assume its gas-weighted forward integral is absolutely integrable. Write $V=|P|/M$. For $V>0$,
--   $$
--   F(P)=\frac2{\sqrt\pi}\int_0^\infty \frac v{v_\beta V}\sinh\left(\frac{2vV}{v_\beta^2}\right)e^{-(v^2+V^2)/v_\beta^2}g(m_*v^2/2)dv.
--   $$
--   At $P=0$ the nonsingular radial expression is $F(0)=\frac4{\sqrt\pi}\int_0^\infty (v^2/v_\beta^3)e^{-v^2/v_\beta^2}g(m_*v^2/2)dv$. This retains the relative-motion energy and the complete thermal averaging factors.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 33, §6.3: Maxwell average of an isotropic forward amplitude, (6.17)

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

/-- PDF pp.32–33, (6.17): exact Maxwell average of an isotropic forward
amplitude, including the separate nonsingular zero-beam-speed formula. -/
theorem isotropic_forwardAverage (d : CollisionData) (beta : ℝ) (hbeta : 0 < beta)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (g : ℝ → ℂ)
    (hf : ∀ p, d.amplitude p p = g (‖p‖ ^ 2 / (2 * reducedMass d.parameters)))
    (P : Momentum)
    (hforward : Integrable (fun p => (d.gas.value p : ℂ) *
      d.amplitude (relativeMomentum d.parameters p P) (relativeMomentum d.parameters p P))) :
    (P ≠ 0 → IntegrableOn (radialForwardIntegrand d.parameters beta (‖P‖ / d.parameters.M) g)
        (Set.Ioi 0) ∧ forwardAverage d P = (2 / Real.sqrt Real.pi : ℝ) *
      ∫ v in Set.Ioi (0 : ℝ), radialForwardIntegrand d.parameters beta (‖P‖ / d.parameters.M) g v) ∧
    (P = 0 → forwardAverage d P = (4 / Real.sqrt Real.pi : ℝ) *
      ∫ v in Set.Ioi (0 : ℝ),
        (v ^ 2 / thermalSpeed d.parameters beta ^ 3 *
          Real.exp (-v ^ 2 / thermalSpeed d.parameters beta ^ 2) : ℝ) *
          g (reducedMass d.parameters * v ^ 2 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
