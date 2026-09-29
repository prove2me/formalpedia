-- Prove2me | Theorems.Thm_RubinSilverberg_rsBeta_sub_mul_rsGamma
-- name    : RubinSilverberg.rsBeta_sub_mul_rsGamma
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/fae95ee4-a0d8-5d4b-a289-42edf177c2aa
-- title:
--   Determinant of the Rubin–Silverberg Möbius datum
-- statement:
--   Let $K$ be a field and $u \in K$ with $u \neq 0$ and $u^{10} + 11u^5 - 1 \neq 0$. Write $f(u) = u^{10} + 11u^5 - 1$, and let $T$ and $H$ be the Klein polynomials $T(u) = u^{30} + 522u^{25} - 10005u^{20} - 10005u^{10} - 522u^5 + 1$ (`kleinT`) and $H(u) = u^{20} - 228u^{15} + 494u^{10} + 228u^5 + 1$ (`kleinH`). With $\beta(u) =$ `rsBeta u` $= T(u)\,(57u^{15} - 247u^{10} - 171u^5 - 1)/(144\,u^4 f(u)^4)$ and $\gamma(u) =$ `rsGamma u` $= T(u)\,(u^{15} - 171u^{10} + 247u^5 + 57)/(144\,f(u)^4)$, the assertion is the identity $$\beta(u) - u\,\gamma(u) = -\frac{T(u)\,H(u)}{144\,u^4 f(u)^4}$$ in $K$. Thus the determinant of $\begin{pmatrix} \beta(u) & u \\ \gamma(u) & 1\end{pmatrix}$ equals the displayed explicit rational expression. No assumption is imposed on the characteristic of $K$; divisions are the field division of Lean, so that in characteristics $2$ and $3$ both sides vanish.
--
--   This is the determinant identity for the Möbius datum $(\beta(u),\gamma(u))$ of the Rubin–Silverberg family, which expresses non-degeneracy of the substitution $t \mapsto (\beta(u)t + u)/(\gamma(u)t + 1)$ off the loci where $T(u)$ or $H(u)$ vanishes. It is used in [`RubinSilverberg.rsMember_Psi3_eval_ne_zero`](thm.html#RubinSilverberg.rsMember_Psi3_eval_ne_zero), where the non-vanishing of this determinant enters the verification that a member of the family is non-degenerate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_rsBeta_sub_mul_rsGamma.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.rsBeta_sub_mul_rsGamma {K : Type*} [Field K] (u : K) (hu : u ≠ 0) (hf : u ^ 10 + 11 * u ^ 5 - 1 ≠ 0) : rsBeta u - u * rsGamma u = -(kleinT u * kleinH u) / (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4) := by sorry
