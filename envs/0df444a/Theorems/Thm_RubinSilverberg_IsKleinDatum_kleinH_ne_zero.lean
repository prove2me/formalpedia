-- Prove2me | Theorems.Thm_RubinSilverberg_IsKleinDatum_kleinH_ne_zero
-- name    : RubinSilverberg.IsKleinDatum.kleinH_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/81bcf068-1b98-569b-9577-8a7e4cce9a5d
-- title:
--   Non-vanishing of H(u₀) for a Klein datum with a ≠ 0
-- statement:
--   Let $K$ be a field of characteristic zero and let $a$, $b$, $u_0$ be elements of $K$. Write $V(u) = u(u^{10} + 11u^5 - 1)$ for `kleinV` and $H(u) = u^{20} - 228u^{15} + 494u^{10} + 228u^5 + 1$ for `kleinH`. Assume that the triple $(a, b, u_0)$ satisfies `IsKleinDatum`, that is, the two conditions
--   $$H(u_0)^3\,(4a^3 + 27b^2) + 6912\,a^3\,V(u_0)^5 = 0, \qquad V(u_0) \neq 0.$$
--   Assume further that $a \neq 0$. Then $H(u_0) \neq 0$. The parameter $b$ enters only through the hypothesis, and no condition on the discriminant quantity $4a^3 + 27b^2$ is imposed beyond what the displayed identity provides.
--
--   Here $V$ and $H$ are (up to normalisation) Klein's icosahedral forms of degrees $11$ and $20$, and the condition `IsKleinDatum` is the equality of $j$-invariants matching the curve $y^2 = x^3 + ax + b$ with the member of the Rubin–Silverberg family parametrised by $u_0$. This non-degeneracy statement is used repeatedly downstream in the construction of the family, for instance in [`RubinSilverberg.Psi3_eval_ne_zero_of_rsFamily`](thm.html#RubinSilverberg.Psi3_eval_ne_zero_of_rsFamily), [`RubinSilverberg.disc_coeff_ne_zero`](thm.html#RubinSilverberg.disc_coeff_ne_zero) and [`RubinSilverberg.exists_torsionBy_linearEquiv_rsMember`](thm.html#RubinSilverberg.exists_torsionBy_linearEquiv_rsMember).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_IsKleinDatum_kleinH_ne_zero.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.IsKleinDatum.kleinH_ne_zero {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (h : RubinSilverberg.IsKleinDatum a b u₀) (ha : a ≠ 0) : RubinSilverberg.kleinH u₀ ≠ 0 := by sorry
