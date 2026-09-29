-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_coeff_nthSeries_eq_mul_hasseInvariant
-- name    : WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/d7f4912b-df74-5826-ab8a-0cbd8b3285ab
-- title:
--   The X^q-coefficient of [q] equals the Hasse invariant
-- statement:
--   Let $q$ be a prime with $q \neq 2$. The assertion is that there is an integer $c$ whose reduction in $\mathbb{Z}/q$ is nonzero such that, for every commutative ring $R$ of characteristic $q$, every Weierstrass curve $W$ over $R$ (given by its coefficients $a_1,a_2,a_3,a_4,a_6$) whose discriminant $W.\Delta$ is a unit, and every formal group $G$ over $R$ whose underlying two-variable power series `G.toPowerSeries` coincides with `W.formalGroupLawFixed` — the Weierstrass formal group law of $W$, obtained by substituting the two-variable series `W.fgZ3Fixed` into the one-variable series `W.fgInv` — one has
--   $$\operatorname{coeff}_{X^q}\bigl(G.\mathrm{nthSeries}\,q\bigr) = c \cdot H_q(W),$$
--   where `G.nthSeries` is defined by $\mathrm{nthSeries}\,0 = 0$ and $\mathrm{nthSeries}(n+1) = G.\mathrm{toPowerSeries}(\mathrm{nthSeries}\,n, X)$, so that $\mathrm{nthSeries}\,q$ is the multiplication-by-$q$ series $[q]_G$, and where $H_q(W) =$ `W.hasseInvariant q` is the coefficient of degree $q-1$ in the $((q-1)/2)$-th power of the polynomial `W.twoTorsionPolynomial.toPoly`. Note that the integer $c$ is chosen once and for all, before the quantifiers over $R$, $W$ and $G$.
--
--   This is Katz's identity expressing the leading coefficient of the multiplication-by-$q$ series of the Weierstrass formal group in characteristic $q$ in terms of the Hasse invariant; its universal form, with the constant fixed ahead of the ring, is what allows it to be applied after base change (for instance to rings with nilpotents). It is the bridge between the formal-group computations and the supersingular locus, and is used downstream in the statements about the $q$-series over quotients and lifts of $R$, such as [`WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two`](thm.html#WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two) and [`WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot`](thm.html#WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_coeff_nthSeries_eq_mul_hasseInvariant.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    ∃ c : ℤ, ((c : ZMod q) ≠ 0) ∧
      ∀ (R : Type) [CommRing R] [CharP R q] (W : WeierstrassCurve R), IsUnit W.Δ → ∀ (G : FormalGroup R),
        G.toPowerSeries = W.formalGroupLawFixed →
          PowerSeries.coeff q (G.nthSeries q) = (c : R) * W.hasseInvariant q := by sorry
