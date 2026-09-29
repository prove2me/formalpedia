-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_a2_checks_addXYZ_crossXZ
-- name    : WeierstrassProjModel.kw_a2_checks_addXYZ_crossXZ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/9531f234-3c51-5efb-aecd-5d858c99fedc
-- title:
--   Chord polynomials give minus the projective addition formulas
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$, and $F$ a field that is an $R$-algebra (in the same universe). Work with the polynomial ring in six variables indexed by $\mathrm{Fin}\,3\oplus\mathrm{Fin}\,3$ over $R$, write $X^{\mathrm l}_i,X^{\mathrm r}_i$ for the left and right variables, and for $P,Q:\mathrm{Fin}\,3\to F$ let $\mathrm{aeval}$ at $\mathrm{Sum.elim}\,P\,Q$ be the $R$-algebra map sending $X^{\mathrm l}_i\mapsto P_i$, $X^{\mathrm r}_i\mapsto Q_i$. Here `kw_lrAdd_X` $=c_{12}X^{\mathrm l}_0-c_{21}X^{\mathrm r}_0$, `kw_lrAdd_Z` $=c_{12}X^{\mathrm l}_2-c_{21}X^{\mathrm r}_2$ and `kw_lrAdd_Y` $=-(c_{12}X^{\mathrm l}_1-c_{21}X^{\mathrm r}_1)-a_1\,$`kw_lrAdd_X`$-a_3\,$`kw_lrAdd_Z`, with $c_{12},c_{21}$ the auxiliary six-variable polynomials of the same module; `kw_lrSym_X` and `kw_lrSym_Z` are the explicitly written polynomials, bihomogeneous of degree $2$ in each triple, with coefficients polynomial in the $a_i$. The assertion is a conjunction of four statements about the base-changed projective curve $(W_F)$: for all $P,Q$, the evaluations of `kw_lrAdd_X`, `kw_lrAdd_Y`, `kw_lrAdd_Z` equal $-\mathrm{addX}(P,Q)$, $-\mathrm{addY}(P,Q)$, $-\mathrm{addZ}(P,Q)$ respectively; and for every $P$ satisfying the projective Weierstrass equation, the diagonal evaluation of `kw_lrSym_X` times $\mathrm{dblZ}(P)$ equals that of `kw_lrSym_Z` times $\mathrm{dblX}(P)$.
--
--   This is the bookkeeping that identifies the module's explicit chord-addition polynomials, up to a global sign, with Mathlib's projective addition formulas $\mathrm{addX},\mathrm{addY},\mathrm{addZ}$ for a Weierstrass curve, together with a cross-multiplied identity comparing the symmetric (doubling) polynomials with $\mathrm{dblX},\mathrm{dblZ}$ on points of the curve. It is used by [`WeierstrassProjModel.kw_a2_checks`](thm.html#WeierstrassProjModel.kw_a2_checks) and by [`WeierstrassProjModel.kw_a2_sixU_class_eq_addMap_of_delta_ne_zero`](thm.html#WeierstrassProjModel.kw_a2_sixU_class_eq_addMap_of_delta_ne_zero), where the polynomial addition law is compared with the geometric group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_a2_checks_addXYZ_crossXZ.lean

import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassProjModel MvPolynomial

theorem WeierstrassProjModel.kw_a2_checks_addXYZ_crossXZ.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] :
    (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_X W) = -((W.baseChange F).toProjective).addX P Q)
    ∧ (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_Y W) = -((W.baseChange F).toProjective).addY P Q)
    ∧ (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_Z W) = -((W.baseChange F).toProjective).addZ P Q)
    ∧ (∀ P : Fin 3 → F, ((W.baseChange F).toProjective).Equation P →
      MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_X W) * ((W.baseChange F).toProjective).dblZ P
      = MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Z W) * ((W.baseChange F).toProjective).dblX P) := by sorry
