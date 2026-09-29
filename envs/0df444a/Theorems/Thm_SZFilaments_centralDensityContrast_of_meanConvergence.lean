-- Prove2me | Theorems.Thm_SZFilaments_centralDensityContrast_of_meanConvergence
-- name    : SZFilaments.centralDensityContrast_of_meanConvergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:35:21.406443+00:00
-- url     : https://prove2.me/theorems/6a16ecc4-6a5e-41e2-a5e5-230a29b43a22
-- title:
--   Eq. (A.5): central matter density contrast from the mean convergence
-- statement:
--   **Equation (A.5) of the paper: the lensing counterpart of the density calibration.**
--
--   The same cylindrical Gaussian model is applied to the total matter, with the Compton parameter replaced by the CMB lensing convergence of Eq. (2). The filament's density contrast follows $\delta(\ell, r_\perp) = \delta_0 \exp(-\ell^2/(2\sigma^2))\exp(-r_\perp^2/(2(\sigma^2+\sigma_B^2)))$ with central contrast $\delta_0$ and intrinsic width $\sigma > 0$, and the convergence is obtained by integrating it along the line of sight against the thin-lens efficiency factor
--   $$\frac{3 H_0^2 \Omega_m}{2c^2}\cdot\frac{D_L(D_S-D_L)}{D_S}\cdot\frac{1}{a}.$$
--   Assume the measured mean convergence $\bar{\kappa}$ obeys the same peak-to-mean calibration as the SZ measurement: the model's convergence on the filament axis equals $\bar{\kappa}/0.9$. Then the central density contrast is
--   $$\delta_0 = \frac{\bar{\kappa}/0.9}{\sqrt{2\pi}\,\sigma}\cdot\frac{2 a c^2}{3 H_0^2 \Omega_m}\cdot\frac{D_S}{D_L(D_S-D_L)}.$$
--   The Hubble constant $H_0$, matter density parameter $\Omega_m$, speed of light $c$ and scale factor $a$ are strictly positive, and the lens lies strictly between the observer and the source, $0 < D_L < D_S$, so the geometric factor is nonzero. The beam width $\sigma_B$ is unconstrained and does not enter the conclusion.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, p. 12, Appendix A, Eq. (A.5); model of Eq. (2), p. 3

import Definitions.Def_szFilamentModel
open MeasureTheory Real

namespace SZFilaments

theorem centralDensityContrast_of_meanConvergence
    (delta0 sigma sigmaB H0 Om c a DL DS kappabar : ℝ) (hsigma : 0 < sigma)
    (hH0 : 0 < H0) (hOm : 0 < Om) (hc : 0 < c) (ha : 0 < a)
    (hDL : 0 < DL) (hDLS : DL < DS)
    (hkappa : convergence (lensingPrefactor H0 Om c a DL DS)
        (fun l => gaussianFilamentProfile delta0 sigma sigmaB l 0) = kappabar / 0.9) :
    delta0 = kappabar / 0.9 / (Real.sqrt (2 * π) * sigma) *
        (2 * a * c ^ 2 / (3 * H0 ^ 2 * Om)) * (DS / (DL * (DS - DL))) := by sorry

end SZFilaments
