-- Prove2me | Theorems.Thm_SZFilaments_centralDensity_of_meanComptonY
-- name    : SZFilaments.centralDensity_of_meanComptonY
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:33:17.622277+00:00
-- url     : https://prove2.me/theorems/f2627e4f-8618-4bcd-8f3c-5651e3e59564
-- title:
--   Eq. (A.3): central electron density from the mean Compton parameter
-- statement:
--   **Equation (A.3) of the paper: the central electron density implied by the measured mean Compton parameter.**
--
--   The paper measures a mean Compton parameter $\bar{y}$ over the filament box and notes that the peak of the one-dimensional profile is close to $\bar{y}/0.9$. Impose that calibration on the Gaussian cylinder model: assume the Compton parameter of the model evaluated on the filament axis ($r_\perp = 0$) equals $\bar{y}/0.9$. Then the central electron density of the model is
--   $$n_0 = \frac{\bar{y}/0.9}{\sqrt{2\pi}\,\sigma}\cdot\frac{m_e c^2}{k_B T_e \sigma_T},$$
--   which is Eq. (A.3). The intrinsic width satisfies $\sigma > 0$ and the physical constants $k_B$, $T_e$, $\sigma_T$, $m_e$, $c$ are all strictly positive; the beam width $\sigma_B$ is unconstrained and does not enter the conclusion, since the calibration is imposed on the axis.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, p. 12, Appendix A, Eq. (A.3)

import Definitions.Def_szFilamentModel
open MeasureTheory Real

namespace SZFilaments

theorem centralDensity_of_meanComptonY
    (n0 sigma sigmaB kB Te sigmaT me c ybar : ℝ) (hsigma : 0 < sigma)
    (hkB : 0 < kB) (hTe : 0 < Te) (hsigmaT : 0 < sigmaT) (hme : 0 < me) (hc : 0 < c)
    (hy : comptonY (szPrefactor kB Te sigmaT me c)
        (fun l => gaussianFilamentProfile n0 sigma sigmaB l 0) = ybar / 0.9) :
    n0 = ybar / 0.9 * (me * c ^ 2 / (kB * Te * sigmaT)) / (Real.sqrt (2 * π) * sigma) := by sorry

end SZFilaments
