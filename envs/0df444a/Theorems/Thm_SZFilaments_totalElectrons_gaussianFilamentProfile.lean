-- Prove2me | Theorems.Thm_SZFilaments_totalElectrons_gaussianFilamentProfile
-- name    : SZFilaments.totalElectrons_gaussianFilamentProfile
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:01:27.282336+00:00
-- url     : https://prove2.me/theorems/50340d9d-ca25-494f-b0d0-a6547dab3df8
-- title:
--   Eq. (A.4): total electron content of a filament
-- statement:
--   **Equation (A.4) of the paper, the goal of this mission: the total electron content of a filament.**
--
--   A filament of length $L$ is modelled as a cylinder whose electron density follows the beam-convolved Gaussian profile of Eq. (A.1), with central density $n_0$, intrinsic width $\sigma > 0$ and beam width $\sigma_B$. Its total electron content is
--   $$N_e = L \iint n_e(\ell, r_\perp)\, d\ell\, dr_\perp.$$
--   Assume the observational calibration of Eq. (A.3): the model's Compton parameter on the filament axis equals $\bar{y}/0.9$, where $\bar{y}$ is the mean Compton parameter measured over the filament region. Then
--   $$N_e = \frac{\bar{y}}{0.9}\cdot\frac{m_e c^2}{k_B T_e \sigma_T}\cdot \sqrt{2\pi}\, L \sqrt{\sigma^2 + \sigma_B^2}.$$
--   This is the master formula of the paper's baryon-content estimate: the measured mean Compton parameter, an assumed gas temperature $T_e$ and the beam width fix the number of electrons in the filament, and hence the baryon fraction it carries. The physical constants $k_B$, $T_e$, $\sigma_T$, $m_e$, $c$ are strictly positive and $\sigma > 0$; the filament length $L$, the beam width $\sigma_B$ and the measured $\bar{y}$ carry no sign assumption. The dependence on the poorly known intrinsic width $\sigma$ enters only through $\sqrt{\sigma^2 + \sigma_B^2}$.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, p. 12, Appendix A, Eq. (A.4)

import Definitions.Def_szFilamentModel
open MeasureTheory Real

namespace SZFilaments

theorem totalElectrons_gaussianFilamentProfile
    (L n0 sigma sigmaB kB Te sigmaT me c ybar : ℝ) (hsigma : 0 < sigma)
    (hkB : 0 < kB) (hTe : 0 < Te) (hsigmaT : 0 < sigmaT) (hme : 0 < me) (hc : 0 < c)
    (hy : comptonY (szPrefactor kB Te sigmaT me c)
        (fun l => gaussianFilamentProfile n0 sigma sigmaB l 0) = ybar / 0.9) :
    totalElectrons L (fun l r => gaussianFilamentProfile n0 sigma sigmaB l r)
      = ybar / 0.9 * (me * c ^ 2 / (kB * Te * sigmaT)) * Real.sqrt (2 * π) * L *
          Real.sqrt (sigma ^ 2 + sigmaB ^ 2) := by sorry

end SZFilaments
