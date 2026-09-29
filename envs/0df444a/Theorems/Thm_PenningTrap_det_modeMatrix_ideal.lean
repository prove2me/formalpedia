-- Prove2me | Theorems.Thm_PenningTrap_det_modeMatrix_ideal
-- name    : PenningTrap.det_modeMatrix_ideal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:06:57.00998+00:00
-- url     : https://prove2.me/theorems/c0bba636-6166-41fe-897c-c75edd8dcee5
-- title:
--   Ideal Penning trap: explicit factorization of $\det M(\omega)$
-- statement:
--   Take the ideal trap: no tilt and no elliptic distortion, i.e.
--
--   $$K=\operatorname{diag}\left(-\tfrac{\omega_z^2}{2},-\tfrac{\omega_z^2}{2},\omega_z^2\right),\qquad b=(0,0,1),$$
--
--   which is the Hessian (divided by the mass) of the quadrupole potential $\propto z^2-\rho^2/2$ with axial frequency $\omega_z$, together with a magnetic field along the trap axis. Assume the standard stability condition $\omega_c^2\ge 2\omega_z^2$ and set $s=\sqrt{\omega_c^2-2\omega_z^2}$. Then for every real $\omega$
--
--   $$\det M(\omega)=-\left(\omega^2-\bar\omega_c^2\right)\left(\omega^2-\omega_z^2\right)\left(\omega^2-\bar\omega_m^2\right),\qquad \bar\omega_c=\frac{\omega_c+s}{2},\quad \bar\omega_m=\frac{\omega_c-s}{2}.$$
--
--   So the ideal trap has the three familiar eigenfrequencies: the trap-modified cyclotron frequency $\bar\omega_c$, the axial frequency $\omega_z$, and the magnetron frequency $\bar\omega_m$, with $\bar\omega_c+\bar\omega_m=\omega_c$ and $\bar\omega_c\bar\omega_m=\omega_z^2/2$.
--
--   Besides being the classical special case, this result exhibits explicit data for which the factorization hypothesis of the invariance theorem holds, so that the general statement is not vacuous.
-- source:
--   X. Fan, T. G. Myers, B. A. D. Sukra, G. Gabrielse, Measurement of the Electron Magnetic Moment, Phys. Rev. Lett. 130, 071801 (2023), arXiv:2209.13084v2, p. 2, Eq. (4) (invariance theorem), with Eq. (2)-(3) for the trap frequencies; original source L. S. Brown and G. Gabrielse, Phys. Rev. A 25, 2423 (1982).

import Mathlib
import Definitions.Def_PenningTrap_model
open Matrix

namespace PenningTrap

theorem det_modeMatrix_ideal (wz wc : ℝ) (h : 2 * wz ^ 2 ≤ wc ^ 2) (w : ℝ) :
    (modeMatrix (Matrix.diagonal ![-(wz ^ 2) / 2, -(wz ^ 2) / 2, wz ^ 2]) ![0, 0, 1] wc w).det
      = -(((w ^ 2 - ((wc + Real.sqrt (wc ^ 2 - 2 * wz ^ 2)) / 2) ^ 2) * (w ^ 2 - wz ^ 2) *
            (w ^ 2 - ((wc - Real.sqrt (wc ^ 2 - 2 * wz ^ 2)) / 2) ^ 2) : ℝ) : ℂ) := by sorry

end PenningTrap
