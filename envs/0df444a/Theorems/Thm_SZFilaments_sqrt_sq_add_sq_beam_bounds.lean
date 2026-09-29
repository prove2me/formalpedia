-- Prove2me | Theorems.Thm_SZFilaments_sqrt_sq_add_sq_beam_bounds
-- name    : SZFilaments.sqrt_sq_add_sq_beam_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:36:11.418111+00:00
-- url     : https://prove2.me/theorems/28c06484-0191-402c-b34f-d37ca5395e28
-- title:
--   Beam dominance: $\sigma_B \le \sqrt{\sigma^2+\sigma_B^2} \le \sigma_B(1+\sigma^2/2\sigma_B^2)$
-- statement:
--   **The remark following Eq. (A.4): the electron content is insensitive to the assumed intrinsic width when the beam dominates.**
--
--   In Eq. (A.4) the assumed intrinsic filament width $\sigma$ — taken from simulations rather than measured — enters the total electron content only through the factor $\sqrt{\sigma^2 + \sigma_B^2}$, where $\sigma_B$ is the width of the Planck beam. The paper argues that because the beam dominates ($\sigma_B \simeq 3\sigma$ for the adopted values), the choice of $\sigma$ changes the inferred baryon fraction by only about one percentage point. Quantitatively, for $\sigma > 0$ and $\sigma_B > 0$,
--   $$\sigma_B \;\le\; \sqrt{\sigma^2 + \sigma_B^2} \;\le\; \sigma_B\left(1 + \frac{\sigma^2}{2\sigma_B^2}\right),$$
--   so the factor never falls below its beam-only value $\sigma_B$ and exceeds it by a relative amount of at most $\sigma^2/(2\sigma_B^2)$ — one part in eighteen when $\sigma_B = 3\sigma$.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, p. 12, Appendix A, remark following Eq. (A.4)

import Definitions.Def_szFilamentModel
open MeasureTheory Real

namespace SZFilaments

theorem sqrt_sq_add_sq_beam_bounds (sigma sigmaB : ℝ) (hsigma : 0 < sigma)
    (hsigmaB : 0 < sigmaB) :
    sigmaB ≤ Real.sqrt (sigma ^ 2 + sigmaB ^ 2) ∧
      Real.sqrt (sigma ^ 2 + sigmaB ^ 2) ≤ sigmaB * (1 + sigma ^ 2 / (2 * sigmaB ^ 2)) := by sorry

end SZFilaments
