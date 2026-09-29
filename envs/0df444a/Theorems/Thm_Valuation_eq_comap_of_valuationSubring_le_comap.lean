-- Prove2me | Theorems.Thm_Valuation_eq_comap_of_valuationSubring_le_comap
-- name    : Valuation.eq_comap_of_valuationSubring_le_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/4afe1611-48d5-53ba-82a4-d533c11f9044
-- title:
--   Normalised valuation determined by a one-sided inclusion of valuation rings
-- statement:
--   Let $L$ and $L'$ be fields, let $v$ be a valuation on $L'$ and $w$ a valuation on $L$, both with values in $\mathbb{Z}^{m0} = \mathrm{WithZero}(\mathrm{Multiplicative}\,\mathbb{Z})$, and assume both are surjective as maps onto this value monoid (i.e. both are normalised discrete valuations, attaining every value $\exp(n)$, $n \in \mathbb{Z}$, as well as $0$). Let $\sigma : L \simeq_{+*} L'$ be a ring isomorphism. The single hypothesis relating the two valuations is the one-sided inclusion of valuation subrings $\mathcal{O}_w \le \sigma^{-1}(\mathcal{O}_v)$, where $\sigma^{-1}(\mathcal{O}_v)$ denotes the comap of `v.valuationSubring` along the ring homomorphism underlying $\sigma$; explicitly, $w(x) \le 1$ implies $v(\sigma x) \le 1$ for all $x \in L$. The conclusion is the equality of valuations $w = v \circ \sigma$ (the comap of $v$ along the ring homomorphism underlying $\sigma$), i.e. $w(x) = v(\sigma x)$ for every $x \in L$, so that in particular the inclusion of hypothesis is in fact an equality.
--
--   This is the standard transport principle for normalised discrete valuations: a discrete valuation ring is a maximal proper subring of its fraction field, so a one-sided domination of valuation rings along an isomorphism forces equality of the normalised valuations. It is used in the function-field computations for elliptic curves, where the valuation at a point is compared with the valuation pulled back along an isomorphism of the function field, and is cited by [`WeierstrassCurve.Affine.valuation_transEquiv_weilFun`](thm.html#WeierstrassCurve.Affine.valuation_transEquiv_weilFun).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Valuation_eq_comap_of_valuationSubring_le_comap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Valuation.eq_comap_of_valuationSubring_le_comap {L L' : Type*} [Field L] [Field L'] {v : Valuation L' (WithZero (Multiplicative ℤ))} {w : Valuation L (WithZero (Multiplicative ℤ))} (hv : Function.Surjective v) (hw : Function.Surjective w) (σ : L ≃+* L') (hle : w.valuationSubring ≤ v.valuationSubring.comap σ.toRingHom) : w = v.comap σ.toRingHom := by sorry
