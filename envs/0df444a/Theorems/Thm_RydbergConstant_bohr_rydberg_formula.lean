-- Prove2me | Theorems.Thm_RydbergConstant_bohr_rydberg_formula
-- name    : RydbergConstant.bohr_rydberg_formula
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:32:05.567257+00:00
-- url     : https://prove2.me/theorems/ee437a7a-96e8-40f9-b029-8ee267c9101d
-- title:
--   Rydberg formula with reduced mass: $\frac1\lambda=R_M\left(\frac1{n_1^2}-\frac1{n_2^2}\right)$
-- statement:
--   Here $K$ is a bundle of five real constants: the electron rest mass $m_e$, the elementary charge $e$, the vacuum permittivity $\varepsilon_0$, the Planck constant $h$ and the speed of light $c$, each assumed strictly positive; no numerical (SI) values are fixed. Let $M>0$ be the mass of the nucleus, $\mu=1/(1/m_e+1/M)$ the reduced mass of the electron and $R_M=(\mu/m_e)R_\infty=\dfrac{R_\infty}{1+m_e/M}$ the corrected Rydberg constant, $R_\infty=\dfrac{m_ee^4}{8\varepsilon_0^2h^3c}$. Let $n_1\neq n_2$ be positive integers and, for $i=1,2$, let $r_i>0$, $v_i>0$ describe a Bohr orbit of mass $\mu$ with quantum number $n_i$:
--
--   $$\frac{\mu v_i^2}{r_i}=\frac{e^2}{4\pi\varepsilon_0r_i^2},\qquad \mu v_ir_i=n_i\hbar,\qquad \hbar=\frac h{2\pi}.$$
--
--   With orbit energies $E_i=\tfrac12\mu v_i^2-\dfrac{e^2}{4\pi\varepsilon_0r_i}$, the photon wavenumber $1/\lambda=(E_2-E_1)/(hc)$ satisfies the Rydberg formula
--
--   $$\frac1\lambda=R_M\left(\frac1{n_1^2}-\frac1{n_2^2}\right).$$
--
--   This is the Bohr-model derivation of the hydrogen spectral series with the reduced-mass correction, as stated in the source's Bohr model section.
--
--   **Formalization Note** The wavenumber is the energy difference divided by $hc$; for $n_2>n_1$ it is the (positive) wavenumber of the emitted photon.
-- source:
--   Wikipedia, "Rydberg constant", revision oldid=1341645811 (https://en.wikipedia.org/w/index.php?title=Rydberg_constant&oldid=1341645811)

import Mathlib
import Definitions.Def_RydbergConstant_Defs

namespace RydbergConstant

theorem bohr_rydberg_formula (K : Constants) (M : ℝ) (hM : 0 < M) (n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hne : n₁ ≠ n₂) (r₁ v₁ r₂ v₂ : ℝ)
    (h₁ : IsBohrOrbit K (reducedMass K M) n₁ r₁ v₁)
    (h₂ : IsBohrOrbit K (reducedMass K M) n₂ r₂ v₂) :
    (orbitEnergy K (reducedMass K M) r₂ v₂ - orbitEnergy K (reducedMass K M) r₁ v₁) /
        (K.h * K.c) =
      rydbergM K M * (1 / (n₁ : ℝ) ^ 2 - 1 / (n₂ : ℝ) ^ 2) := by sorry

end RydbergConstant
