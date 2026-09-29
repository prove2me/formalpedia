-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isUnit_nthSeries_eq_mul_X_npow_of_variableChange
-- name    : WeierstrassCurve.exists_isUnit_nthSeries_eq_mul_X_npow_of_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/f5f22cd8-eb8c-5574-bbd8-c530f69b7ce3
-- title:
--   Shape [q]=u· Xⁿ is invariant under Weierstrass coordinate change
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$, $C$ a Weierstrass variable change over $R$, and let $q$ and $n$ be natural numbers (no relation between them is assumed). Let $F$ and $F'$ be formal group laws over $R$ whose underlying two-variable power series are, respectively, $W$'s Weierstrass formal group law `W.formalGroupLawFixed` and that of the transformed curve `C • W`; here `formalGroupLawFixed` is obtained by substituting the series `fgZ3Fixed` (built from $-X_0-X_1$ and the correction term `fgZ3NumFixed * invOfUnit fgZ3Denom 1`) into the inversion series `fgInv` $=-X\cdot$`invOfUnit fgInvDenom 1`. For a formal group law $G$, `G.nthSeries` is defined by `nthSeries 0 = 0` and `nthSeries (m+1) = subst ![nthSeries m, X] G.toPowerSeries`, that is, the multiplication-by-$m$ series $[m]_G(X)$. The hypothesis is that there exists a unit $u$ of $R⟦X⟧$ with $F.\mathrm{nthSeries}\,q = u\cdot X^{n}$. The conclusion asserts the existence of a unit $u'$ of $R⟦X⟧$ with $F'.\mathrm{nthSeries}\,q = u'\cdot X^{n}$.
--
--   The statement records that the divisibility shape of the multiplication-by-$q$ series of a Weierstrass formal group — and hence the height of the formal group in characteristic $p$ — is unchanged when the curve is replaced by an isomorphic Weierstrass model. It is applied with $n=q$ (ordinary case) and $n=q^{2}$ (height two, supersingular case) in order to transport such information between two Weierstrass representatives of the same isomorphism class of rigid level data on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isUnit_nthSeries_eq_mul_X_npow_of_variableChange.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.exists_isUnit_nthSeries_eq_mul_X_npow_of_variableChange
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (q n : ℕ)
    (F F' : FormalGroup R) (hF : F.toPowerSeries = W.formalGroupLawFixed)
    (hF' : F'.toPowerSeries = (C • W).formalGroupLawFixed)
    (h : ∃ u : PowerSeries R, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ n) :
    ∃ u : PowerSeries R, IsUnit u ∧ F'.nthSeries q = u * PowerSeries.X ^ n := by sorry
