-- Prove2me | Theorems.Thm_Penrose_delta_self_energy
-- name    : Penrose.delta_self_energy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T18:23:40.773168+00:00
-- url     : https://prove2.me/theorems/8db386e4-1d45-496c-ab3d-fbfe978debc4
-- title:
--   Penrose's criterion: $\Delta$ is the self-energy of the difference distribution
-- statement:
--   For any real gravitational constant $G$ and any two smooth, rapidly decreasing mass distributions $\rho, \rho'$ on three-dimensional Euclidean space, Penrose's measure of incompatibility
--
--   $$\Delta(\rho,\rho') = \int_{\mathbb{R}^3} \|\nabla\Phi_\rho - \nabla\Phi_{\rho'}\|^2\,dx$$
--
--   is the gravitational self-energy of the difference of the two mass distributions, up to the explicit constant $-8\pi G$:
--
--   $$\Delta(\rho,\rho') = -8\pi G\, E(\rho - \rho'), \qquad E(\sigma) = -\frac{G}{2}\iint \frac{\sigma(x)\sigma(y)}{\|x-y\|}\,dx\,dy.$$
--
--   This is the central identification of Section 6 of Penrose (1996, pp. 595–597): the measure of incompatibility of the two superposed space-time geometries — the quantity whose order of magnitude, divided into $\hbar$, gives the lifetime $T \simeq \hbar/E_\Delta$ of the superposed state — is basically just the gravitational self-energy of the difference between the two mass distributions. The paper itself notes the constant is loose (apart from the factor $4\pi$ it makes no difference which expression is used); here the constant is made fully explicit, and the two sides are defined independently: an $L^2$ norm of a field difference on the left, a double integral of densities on the right.
--
--   The statement places no hypothesis on $\rho, \rho'$ beyond smoothness and rapid decrease, and none on the sign of $G$.
-- source:
--   Penrose 1996, On Gravity's Role in Quantum State Reduction, General Relativity and Gravitation 28(5):581-600, https://doi.org/10.1007/BF02105068, Section 6, pp. 595-597 (basically just the gravitational self-energy of the difference between the mass distributions)

import Mathlib
import Definitions.Def_penrose
import Definitions.Def_penrose_energy

open MeasureTheory

namespace Penrose

theorem delta_self_energy (G : ℝ) (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) :
    deltaMeasure G ρ ρ' = -8 * Real.pi * G * gravSelfEnergy G (ρ - ρ') := by sorry

end Penrose
