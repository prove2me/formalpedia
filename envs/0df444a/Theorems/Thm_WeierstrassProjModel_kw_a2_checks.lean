-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_a2_checks
-- name    : WeierstrassProjModel.kw_a2_checks
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/30b9d1a3-b4d7-562a-94ac-233c114f581d
-- title:
--   Projective addition-law polynomials evaluate to the negated formulas
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$, and $F$ a field which is an $R$-algebra. Write $E$ for the projective Weierstrass curve $(W_{/F})^{\mathrm{proj}}$ obtained by base change of $W$ to $F$ (this is what `kw_lrApt_WF W F` denotes), with Mathlib's projective addition formulas `addX`, `addY`, `addZ`, doubling formulas `dblX`, `dblY`, `dblZ` and defining equation `Equation`. The polynomials involved live in $R[X_{l,0},X_{l,1},X_{l,2},X_{r,0},X_{r,1},X_{r,2}]$, indexed by $\mathrm{Fin}\,3\oplus\mathrm{Fin}\,3$: the chord polynomials are $\mathtt{kw\_lrAdd\_X}=c_{12}X_{l,0}-c_{21}X_{r,0}$, $\mathtt{kw\_lrAdd\_Z}=c_{12}X_{l,2}-c_{21}X_{r,2}$ and $\mathtt{kw\_lrAdd\_Y}=-(c_{12}X_{l,1}-c_{21}X_{r,1})-a_1\,\mathtt{kw\_lrAdd\_X}-a_3\,\mathtt{kw\_lrAdd\_Z}$, while $\mathtt{kw\_lrSym\_X}$, $\mathtt{kw\_lrSym\_Y}$, $\mathtt{kw\_lrSym\_Z}$ are the explicitly written bihomogeneous forms of bidegree $(2,2)$ with coefficients polynomial in the $a_i$. The assertion is the conjunction of five identities: for all $P,Q\colon \mathrm{Fin}\,3\to F$, evaluation of $\mathtt{kw\_lrAdd\_X}$, $\mathtt{kw\_lrAdd\_Y}$, $\mathtt{kw\_lrAdd\_Z}$ at the pair $(P,Q)$ (left variables at $P$, right at $Q$, coefficients mapped to $F$) gives $-E.\mathrm{addX}(P,Q)$, $-E.\mathrm{addY}(P,Q)$, $-E.\mathrm{addZ}(P,Q)$ respectively; and for every $P$ satisfying the Weierstrass equation of $E$, the cross-multiplied identities $\mathtt{kw\_lrSym\_X}(P,P)\cdot E.\mathrm{dblZ}(P)=\mathtt{kw\_lrSym\_Z}(P,P)\cdot E.\mathrm{dblX}(P)$ and $\mathtt{kw\_lrSym\_Y}(P,P)\cdot E.\mathrm{dblZ}(P)=\mathtt{kw\_lrSym\_Z}(P,P)\cdot E.\mathrm{dblY}(P)$ hold.
--
--   This is the compatibility check identifying the two addition laws of the projective Weierstrass model — the chord law and the symmetric (doubling) law — with the projective addition and doubling formulas of the base-changed curve, up to an overall sign in the first three conjuncts and up to the projective rescaling recorded by the two cross-multiplied identities in the last two. It is used in the construction of the group law morphism on the projective model, via [`WeierstrassProjModel.kw_a2_productMap_sixU_inl_eq_neg_add`](thm.html#WeierstrassProjModel.kw_a2_productMap_sixU_inl_eq_neg_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_a2_checks.lean

import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.kw_a2_checks.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] :
    (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_X W) = -(kw_lrApt_WF W F).addX P Q)
    ∧ (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_Y W) = -(kw_lrApt_WF W F).addY P Q)
    ∧ (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_Z W) = -(kw_lrApt_WF W F).addZ P Q)
    ∧ (∀ P : Fin 3 → F, (kw_lrApt_WF W F).Equation P →
      MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_X W) * (kw_lrApt_WF W F).dblZ P
      = MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Z W) * (kw_lrApt_WF W F).dblX P)
    ∧ (∀ P : Fin 3 → F, (kw_lrApt_WF W F).Equation P →
      MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Y W) * (kw_lrApt_WF W F).dblZ P
      = MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Z W) * (kw_lrApt_WF W F).dblY P) := by sorry
