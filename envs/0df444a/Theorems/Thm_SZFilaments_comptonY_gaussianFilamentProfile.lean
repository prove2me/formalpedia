-- Prove2me | Theorems.Thm_SZFilaments_comptonY_gaussianFilamentProfile
-- name    : SZFilaments.comptonY_gaussianFilamentProfile
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:26:40.985335+00:00
-- url     : https://prove2.me/theorems/e3f7b697-a397-49ce-8874-96823906c3db
-- title:
--   Eq. (A.2): Compton $y$ profile of a Gaussian filament
-- statement:
--   **Equation (A.2) of the paper: the Compton-$y$ profile produced by the Gaussian cylinder model.**
--
--   Consider a filament whose electron density follows the beam-convolved Gaussian cylinder profile of Eq. (A.1),
--   $$n_e(\ell, r_\perp) = n_0 \exp\!\left(-\frac{\ell^2}{2\sigma^2}\right)\exp\!\left(-\frac{r_\perp^2}{2(\sigma^2+\sigma_B^2)}\right),$$
--   with central density $n_0$, intrinsic width $\sigma > 0$ and beam width $\sigma_B$. Integrating it along the line of sight and multiplying by the thermal SZ prefactor $k_B T_e \sigma_T/(m_e c^2)$ of Eq. (1) gives, at every transverse offset $r_\perp$,
--   $$y(r_\perp) = \sqrt{2\pi}\, n_0 \sigma \cdot \frac{k_B T_e \sigma_T}{m_e c^2} \cdot \exp\!\left(-\frac{r_\perp^2}{2(\sigma^2+\sigma_B^2)}\right).$$
--   The transverse Gaussian survives untouched; the line-of-sight direction contributes the factor $\sqrt{2\pi}\,\sigma$. No sign or positivity assumption is placed on $n_0$, $\sigma_B$ or the physical constants: only $\sigma > 0$ is needed for the line-of-sight integral to have this value.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, p. 12, Appendix A, Eq. (A.2)

import Definitions.Def_szFilamentModel
open MeasureTheory Real

namespace SZFilaments

theorem comptonY_gaussianFilamentProfile
    (n0 sigma sigmaB kB Te sigmaT me c r : ℝ) (hsigma : 0 < sigma) :
    comptonY (szPrefactor kB Te sigmaT me c)
        (fun l => gaussianFilamentProfile n0 sigma sigmaB l r)
      = Real.sqrt (2 * π) * n0 * sigma * (kB * Te * sigmaT / (me * c ^ 2)) *
          Real.exp (-r ^ 2 / (2 * (sigma ^ 2 + sigmaB ^ 2))) := by sorry

end SZFilaments
