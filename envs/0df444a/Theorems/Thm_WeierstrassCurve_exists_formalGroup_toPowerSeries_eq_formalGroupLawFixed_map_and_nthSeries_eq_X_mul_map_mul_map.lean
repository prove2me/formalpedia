-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map
-- name    : WeierstrassCurve.exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/12c87a76-cc40-5cad-811f-4c6544465c51
-- title:
--   Base change of an Igusa-type factorisation of [q]
-- statement:
--   Let $S$ and $T$ be commutative rings, $\Phi : S \to T$ a ring homomorphism, and $V$ a Weierstrass curve over $S$. Let $F_S$ be a formal group law over $S$ whose underlying two-variable power series equals $V.\mathrm{formalGroupLawFixed}$, that is, the substitution of $V$'s series $\mathrm{fgZ3Fixed} = -X_0 - X_1 + \mathrm{fgZ3NumFixed}\cdot \mathrm{invOfUnit}(\mathrm{fgZ3Denom},1)$ into the one-variable series $\mathrm{fgInv} = -X\cdot \mathrm{invOfUnit}(\mathrm{fgInvDenom},1)$. Let $q$ be a natural number, $g \in S[X]$ a polynomial and $v \in S[[X]]$ a power series such that the $q$-th iterated series of $F_S$ — defined by $\mathrm{nthSeries}\,0 = 0$ and $\mathrm{nthSeries}\,(n+1) = F_S(\mathrm{nthSeries}\,n, X)$, so that for $q \ge 1$ it is the multiplication-by-$q$ series — factors as $X \cdot g \cdot v$, with $g$ viewed in $S[[X]]$. The conclusion asserts the existence of a formal group law $F_T$ over $T$ whose underlying series is $(V.\mathrm{map}\,\Phi).\mathrm{formalGroupLawFixed}$, the corresponding series of the base-changed Weierstrass curve, and whose $q$-th iterated series factors as $X \cdot (g.\mathrm{map}\,\Phi) \cdot \mathrm{PowerSeries.map}\,\Phi\,v$.
--
--   This records that a factorisation of the multiplication-by-$q$ series of the formal group of a Weierstrass curve, of the shape used in Igusa-type arguments about the formal group along the ordinary locus, is preserved under an arbitrary base change of the coefficient ring. It is used in the analysis of completions of moduli of elliptic curves with full level structure, where such factorisations over a base ring are transported to quotients or localisations of it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem WeierstrassCurve.exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map
    {S T : Type} [CommRing S] [CommRing T] (Φ : S →+* T)
    (V : WeierstrassCurve S) (FS : FormalGroup S) (hFS : FS.toPowerSeries = V.formalGroupLawFixed)
    (q : ℕ) (g : S[X]) (v : PowerSeries S)
    (hfacq : FS.nthSeries q = PowerSeries.X * (↑g : PowerSeries S) * v) :
    ∃ FT : FormalGroup T, FT.toPowerSeries = (V.map Φ).formalGroupLawFixed ∧
      FT.nthSeries q = PowerSeries.X * (↑(g.map Φ) : PowerSeries T) * PowerSeries.map Φ v := by sorry
