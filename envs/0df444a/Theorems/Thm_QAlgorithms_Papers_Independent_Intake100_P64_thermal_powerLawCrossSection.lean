-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_thermal_powerLawCrossSection
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.thermal_powerLawCrossSection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:24:24.902617+00:00
-- url     : https://prove2.me/theorems/abd8a261-c8e6-48d1-bb72-dcccbecb10b1
-- title:
--   §4.3.3: thermal power-law cross-section integral, (4.45)–(4.50)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   Let the differential scattering law be $c|v-V|^a$, with $c>0$ and $a>-4$. Let $\Gamma(P)=4\pi c n_{\rm gas}\int\mu_\beta(p)|p/m-P/M|^{a+1}dp$; its integrand is integrable, with an arbitrary zero value at the single singular relative-velocity point. For $P\ne0$, define $\sigma_{\rm eff}(P)=\Gamma(P)/(n_{\rm gas}|P|/M)$. Then
--   $$
--   \sigma_{\rm eff}(P)=8\sqrt\pi\,\Gamma(a/2+2)\frac{Mc\,v_\beta^{a+1}}{|P|}\,{}_1F_1\left(-\frac{a+1}{2};\frac32;-\frac{|P|^2}{M^2v_\beta^2}\right).
--   $$
--   Multiplication by $n_{\rm gas}|P|/M$ gives a finite rate formula also at zero momentum. Here $\Gamma(\cdot)$ is Euler's gamma function and ${}_1F_1$ is the standard absolutely convergent rising-factorial series. For $a=0$, $\sigma_{\rm tot}=4\pi c$, this is (4.48); for $x\ne0$, ${}_1F_1(-1/2;3/2;-x^2)=e^{-x^2}/2+(1+2x^2)\sqrt\pi\operatorname{erf}(x)/(4x)$, with value $1$ at $x=0$. Along any unit direction, $\lim_{V\downarrow0}V\sigma_{\rm eff}(MV)=\sigma_{\rm tot}\sqrt{8/(\pi m\beta)}$. This distinguishes the finite collision rate from the singular effective cross-section.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 22, §4.3.3: thermal power-law cross-section integral, (4.45)–(4.50)

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

/-- PDF pp.21–22, (4.45)–(4.50), cited antecedent [106]: exact thermal
power-law convolution on its convergence domain a>-4. The 1/V statement is
a limit for the constant-cross-section case, not an equality at finite V. -/
theorem thermal_powerLawCrossSection (a : GasTracerParameters) (beta c exponent : ℝ)
    (hbeta : 0 < beta) (hc : 0 < c) (hexponent : -4 < exponent) :
    (∀ P, Integrable (fun p => maxwell a.m beta p * speedPower a exponent P p)) ∧
    (∀ P, powerCollisionRate a beta c exponent P =
      8 * Real.sqrt Real.pi * a.density * c * Real.Gamma (exponent / 2 + 2) *
        Real.rpow (thermalSpeed a beta) (exponent + 1) *
          kummer (-(exponent + 1) / 2) (3 / 2)
            (-((‖P‖ / (a.M * thermalSpeed a beta)) ^ 2))) ∧
    (∀ P, P ≠ 0 → effectiveCrossSection a beta c exponent P =
      8 * Real.sqrt Real.pi * Real.Gamma (exponent / 2 + 2) * a.M * c *
        Real.rpow (thermalSpeed a beta) (exponent + 1) / ‖P‖ *
          kummer (-(exponent + 1) / 2) (3 / 2)
            (-((‖P‖ / (a.M * thermalSpeed a beta)) ^ 2))) ∧
    (∀ x : ℝ, x ≠ 0 → kummer (-1 / 2) (3 / 2) (-(x ^ 2)) =
      Real.exp (-(x ^ 2)) / 2 +
        (1 + 2 * x ^ 2) * Real.sqrt Real.pi * errorFunction x / (4 * x)) ∧
    (∀ P : Momentum, P ≠ 0 → effectiveCrossSection a beta c 0 P =
      (4 * Real.pi * c) * 2 / Real.sqrt Real.pi * a.M * thermalSpeed a beta / ‖P‖ *
        kummer (-1 / 2) (3 / 2) (-((‖P‖ / (a.M * thermalSpeed a beta)) ^ 2))) ∧
    (exponent = 0 → ∀ axis : Momentum, ‖axis‖ = 1 →
      Tendsto (fun v : ℝ => v * effectiveCrossSection a beta c exponent ((a.M * v) • axis))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (8 * Real.sqrt Real.pi * c * thermalSpeed a beta))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
