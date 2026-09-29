-- Prove2me | Theorems.Thm_RubinSilverberg_exists_int_kleinVHom_ne_zero
-- name    : RubinSilverberg.exists_int_kleinVHom_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/afa44fa0-ac53-5ddb-b74e-08925a5a3fbe
-- title:
--   An integer slope with non-vanishing homogenised Klein form
-- statement:
--   Let $K$ be a field of characteristic zero and let $\beta,\gamma,u_0\in K$. Write $V(u)=u(u^{10}+11u^5-1)$ for the one-variable form `kleinV` and $V_{\mathrm{hom}}(n,d)=nd\,(n^{10}+11n^5d^5-d^{10})$ for the two-variable form `kleinVHom`. Assume $V(u_0)=u_0(u_0^{10}+11u_0^5-1)\neq 0$. The assertion is that there exists an integer $l$ with
--   $$(\beta+l u_0)(\gamma+l)\bigl((\beta+l u_0)^{10}+11(\beta+l u_0)^5(\gamma+l)^5-(\gamma+l)^{10}\bigr)\neq 0,$$
--   that is, $V_{\mathrm{hom}}(\beta+l u_0,\gamma+l)\neq 0$, where the integer $l$ acts on $K$ through the canonical ring map $\mathbb{Z}\to K$. Only existence of one such $l$ is asserted, not that all but finitely many integers work; the $l$ produced by the proof is in fact a positive integer.
--
--   Here $V$ and $V_{\mathrm{hom}}$ are Klein's icosahedral vertex form and its homogenisation, and the statement says that a suitable integral slope can be chosen so that the corresponding point of the projective line avoids the vertex locus. It is used in the construction of an auxiliary elliptic curve in [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists), where the slope parametrises a Möbius reparametrisation of a Rubin–Silverberg family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_exists_int_kleinVHom_ne_zero.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.exists_int_kleinVHom_ne_zero {K : Type*} [Field K] [CharZero K] (β γ u₀ : K) (hV : kleinV u₀ ≠ 0) : ∃ l : ℤ, kleinVHom (β + l * u₀) (γ + l) ≠ 0 := by sorry
