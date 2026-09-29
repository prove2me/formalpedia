-- Prove2me | Theorems.Thm_RubinSilverberg_kleinSection_independent
-- name    : RubinSilverberg.kleinSection_independent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/467246de-35fc-5944-a5d9-f1fd79b506a3
-- title:
--   Independence of the two Klein sections modulo 5
-- statement:
--   Let $K$ be a field of characteristic zero (with decidable equality), let $\zeta \in K$ be a primitive fifth root of unity, and let $u \in K$ satisfy $\mathrm{kleinV}(u) = u(u^{10} + 11u^5 - 1) \neq 0$. Write $B_u$ for the Weierstrass curve `kleinCurve u` over $K$ with $a_1 = a_2 = a_3 = 0$, $a_4 = -\mathrm{kleinH}(u)/48$ and $a_6 = \mathrm{kleinT}(u)/864$, where $\mathrm{kleinH}(u) = u^{20} - 228u^{15} + 494u^{10} + 228u^5 + 1$ and $\mathrm{kleinT}(u) = u^{30} + 522u^{25} - 10005u^{20} - 10005u^{10} - 522u^5 + 1$. For $w \in K$ let $\mathrm{kleinX}(w)$ and $\mathrm{kleinY}(w)$ be the explicit degree $10$ and degree $13$ rational expressions in $w$ given by the definitions, and let $\mathrm{pt}$ denote the point of the affine group $B_u$ with these coordinates when the pair is nonsingular on $B_u$, and the point at infinity otherwise. The assertion is that for all integers $i, j$, if
--   $$i \cdot \mathrm{pt}(B_u; \mathrm{kleinX}(u), \mathrm{kleinY}(u)) + j \cdot \mathrm{pt}(B_u; \mathrm{kleinX}(\zeta u), \mathrm{kleinY}(\zeta u)) = 0$$
--   in the group of affine points of $B_u$, then $5 \mid i$ and $5 \mid j$.
--
--   This is the linear independence over $\mathbb{F}_5$ of the two Rubin–Silverberg sections $Q_u = (\mathrm{kleinX}(u), \mathrm{kleinY}(u))$ and $R_u = Q_{\zeta u}$ on Klein's curve $B_u$, both of which lie on the same curve because $\mathrm{kleinH}$ and $\mathrm{kleinT}$ are polynomials in $u^5$; together with the fact that each has order dividing $5$ and is nonzero, recorded in [`RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul`](thm.html#RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul), it exhibits a copy of $(\mathbb{Z}/5)^2$ inside $B_u[5]$, i.e. the level-$5$ structure of the family. It is used by [`RubinSilverberg.rsMember_sections_independent`](thm.html#RubinSilverberg.rsMember_sections_independent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_kleinSection_independent.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.kleinSection_independent {K : Type*} [Field K] [CharZero K] [DecidableEq K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) (u : K) (hV : kleinV u ≠ 0) (i j : ℤ) (h : i • pt (kleinCurve u) (kleinX u) (kleinY u) + j • pt (kleinCurve u) (kleinX (ζ * u)) (kleinY (ζ * u)) = 0) : (5 : ℤ) ∣ i ∧ (5 : ℤ) ∣ j := by sorry
