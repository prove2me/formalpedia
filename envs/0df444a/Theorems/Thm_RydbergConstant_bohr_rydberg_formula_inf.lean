-- Prove2me | Theorems.Thm_RydbergConstant_bohr_rydberg_formula_inf
-- name    : RydbergConstant.bohr_rydberg_formula_inf
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:25:28.963469+00:00
-- url     : https://prove2.me/theorems/04f53127-f2e7-42c5-a33b-072fd7f6fe49
-- title:
--   Rydberg formula in the Bohr model (infinite nuclear mass)
-- statement:
--   Here $K$ is a bundle of five real constants: the electron rest mass $m_e$, the elementary charge $e$, the vacuum permittivity $\varepsilon_0$, the Planck constant $h$ and the speed of light $c$, each assumed strictly positive; no numerical (SI) values are fixed. Let $n_1\neq n_2$ be positive integers and consider two Bohr orbits of an electron of mass $m_e$ about an infinitely heavy charge $+e$, with quantum numbers $n_1$ and $n_2$, radii $r_i>0$, speeds $v_i>0$, satisfying $m_ev_i^2/r_i=e^2/(4\pi\varepsilon_0r_i^2)$ and $m_ev_ir_i=n_i\hbar$. With orbit energies $E_i=\tfrac12m_ev_i^2-e^2/(4\pi\varepsilon_0r_i)$ and photon wavenumber $1/\lambda=(E_2-E_1)/(hc)$,
--
--   $$\frac1\lambda=\mathrm{Ry}\cdot\frac1{hc}\left(\frac1{n_1^2}-\frac1{n_2^2}\right)=\frac{m_ee^4}{8\varepsilon_0^2h^3c}\left(\frac1{n_1^2}-\frac1{n_2^2}\right).$$
--
--   **Formalization Note** The wavenumber of the photon is taken to be the energy difference of the two orbits divided by $hc$ (Planck–Einstein relation); for $n_2>n_1$ it is positive (emission from $n_2$ to $n_1$), otherwise its absolute value is the wavenumber of the absorbed photon.
-- source:
--   Wikipedia, "Rydberg constant", revision oldid=1341645811 (https://en.wikipedia.org/w/index.php?title=Rydberg_constant&oldid=1341645811)

import Mathlib
import Definitions.Def_RydbergConstant_Defs

namespace RydbergConstant

theorem bohr_rydberg_formula_inf (K : Constants) (n₁ n₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hne : n₁ ≠ n₂) (r₁ v₁ r₂ v₂ : ℝ)
    (h₁ : IsBohrOrbit K K.me n₁ r₁ v₁) (h₂ : IsBohrOrbit K K.me n₂ r₂ v₂) :
    (orbitEnergy K K.me r₂ v₂ - orbitEnergy K K.me r₁ v₁) / (K.h * K.c) =
        rydbergEnergy K * (1 / (K.h * K.c)) * (1 / (n₁ : ℝ) ^ 2 - 1 / (n₂ : ℝ) ^ 2) ∧
    (orbitEnergy K K.me r₂ v₂ - orbitEnergy K K.me r₁ v₁) / (K.h * K.c) =
        K.me * K.e ^ 4 / (8 * K.ε0 ^ 2 * K.h ^ 3 * K.c) *
          (1 / (n₁ : ℝ) ^ 2 - 1 / (n₂ : ℝ) ^ 2) := by sorry

end RydbergConstant
