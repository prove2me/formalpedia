-- Prove2me | Theorems.Thm_SharingPlatform_WageSchemes_price_dcr_vs_fw
-- name    : SharingPlatform.WageSchemes.price_dcr_vs_fw
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:57.062804+00:00
-- url     : https://prove2.me/theorems/cd005568-78ce-488c-bf9c-4f781e2b6701
-- title:
--   Proof of Proposition 3, A.8, p. 52 (PDF 53) — p^{W*} − p^{D*} in closed form; p^{W*} ≥ p^{D*} iff bm ≥ cl
-- statement:
--   Let $p^{D*}$ be the DCR equilibrium price (4) and $p^{W*}$ the FW equilibrium price (9). Under the standing assumptions,
--
--   $$p^{W*} - p^{D*} = \frac{bm(l+m)(am-ck)(bm-cl)}{c\,D_1 D_2},$$
--
--   where $D_1 = b\big(c(l+2m) + m(l+m)\big) + c\big(c(l+2m) + 2m(l+m)\big)$ and $D_2 = b\big(2c(l+2m) + m(2l+3m)\big) + c\big(c(l+2m) + 2m(l+m)\big)$. Consequently $p^{D*} \le p^{W*}$ if and only if $cl \le bm$, and $p^{D*} < p^{W*}$ if and only if $cl < bm$.
--
--   This is the DCR-versus-FW price comparison that, combined with the monotonicity of profit in price, orders $\pi^{D*}$ and $\pi^{W*}$.
--
--   **Formalization Note** The printed denominator has one unbalanced parenthesis; the reading above is the one that agrees with (4) and (9) (checked symbolically). The strict version is added, since Proposition 3 needs it.
-- source:
--   Zhang, Chen, Raghunathan, Two-Sided Platform Competition in a Sharing Economy, SSRN 3555993, proof of Proposition 3, A.8, p. 52 (PDF 53), display of p^{W*} − p^{D*}

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

namespace SharingPlatform.WageSchemes

theorem price_dcr_vs_fw (P : Params) (hP : P.Standing) :
    pW P - pD P =
      P.b * P.m * (P.l + P.m) * (P.a * P.m - P.c * P.k) * (P.b * P.m - P.c * P.l) /
        (P.c * (P.b * (P.c * (P.l + 2 * P.m) + P.m * (P.l + P.m)) +
            P.c * (P.c * (P.l + 2 * P.m) + 2 * P.m * (P.l + P.m))) *
          (P.b * (2 * P.c * (P.l + 2 * P.m) + P.m * (2 * P.l + 3 * P.m)) +
            P.c * (P.c * (P.l + 2 * P.m) + 2 * P.m * (P.l + P.m)))) ∧
    (pD P ≤ pW P ↔ P.c * P.l ≤ P.b * P.m) ∧
    (pD P < pW P ↔ P.c * P.l < P.b * P.m) := by sorry
end SharingPlatform.WageSchemes
