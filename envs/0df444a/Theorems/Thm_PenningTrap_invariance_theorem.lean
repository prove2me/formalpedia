-- Prove2me | Theorems.Thm_PenningTrap_invariance_theorem
-- name    : PenningTrap.invariance_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:07:23.55823+00:00
-- url     : https://prove2.me/theorems/1c908f0a-e74f-4e9b-827c-72ecee6cdab1
-- title:
--   Brown-Gabrielse invariance theorem: $\bar\omega_c^2+\bar\omega_z^2+\bar\omega_m^2=\omega_c^2$
-- statement:
--   This is the invariance theorem of Brown and Gabrielse, Eq. (4) of the electron magnetic moment measurement.
--
--   Let $K$ be a real $3\times3$ matrix that is symmetric (it is the Hessian of the electrostatic potential, divided by the mass) and traceless (Laplace's equation), let $b\in\mathbb{R}^3$ satisfy $\langle b,b\rangle=1$ (the direction of the magnetic field), and let $\omega_c$ be the free-space cyclotron frequency. Suppose the real numbers $\bar\omega_c,\bar\omega_z,\bar\omega_m$ are the eigenfrequencies of the trap, in the sense that
--
--   $$\det M(\omega)=-\big(\omega^2-\bar\omega_c^2\big)\big(\omega^2-\bar\omega_z^2\big)\big(\omega^2-\bar\omega_m^2\big)\qquad\text{for all }\omega\in\mathbb{R}.$$
--
--   Then
--
--   $$\bar\omega_c^{\,2}+\bar\omega_z^{\,2}+\bar\omega_m^{\,2}=\omega_c^{\,2},$$
--
--   equivalently $\nu_c=\sqrt{\bar\nu_c^2+\bar\nu_z^2+\bar\nu_m^2}$ in ordinary frequencies.
--
--   The force of the statement is what it does *not* assume: apart from symmetry and tracelessness, $K$ is arbitrary, so the potential may be tilted at any angle relative to the magnetic field and elliptically distorted to any degree. The three observed frequencies shift individually under such imperfections, but the sum of their squares does not move. This invariance is what allows the free-space cyclotron frequency to be recovered from an imperfect trap, and hence the electron magnetic moment to be measured to parts in $10^{13}$.
--
--   **Formalization Note.** "The eigenfrequencies are $\bar\omega_c,\bar\omega_z,\bar\omega_m$" is formalized as the factorization identity above, valid for every real $\omega$, which records the roots with multiplicity; no sign conditions are imposed on the three frequencies, and the conclusion involves only their squares.
-- source:
--   X. Fan, T. G. Myers, B. A. D. Sukra, G. Gabrielse, Measurement of the Electron Magnetic Moment, Phys. Rev. Lett. 130, 071801 (2023), arXiv:2209.13084v2, p. 2, Eq. (4) (invariance theorem), with Eq. (2)-(3) for the trap frequencies; original source L. S. Brown and G. Gabrielse, Phys. Rev. A 25, 2423 (1982).

import Mathlib
import Definitions.Def_PenningTrap_model
open Matrix

namespace PenningTrap

theorem invariance_theorem (K : Matrix (Fin 3) (Fin 3) ℝ) (hK : K.IsSymm) (hL : K.trace = 0)
    (b : Fin 3 → ℝ) (hb : b ⬝ᵥ b = 1) (wc wbc wbz wbm : ℝ)
    (hfac : ∀ w : ℝ, (modeMatrix K b wc w).det
      = -(((w ^ 2 - wbc ^ 2) * (w ^ 2 - wbz ^ 2) * (w ^ 2 - wbm ^ 2) : ℝ) : ℂ)) :
    wbc ^ 2 + wbz ^ 2 + wbm ^ 2 = wc ^ 2 := by sorry

end PenningTrap
