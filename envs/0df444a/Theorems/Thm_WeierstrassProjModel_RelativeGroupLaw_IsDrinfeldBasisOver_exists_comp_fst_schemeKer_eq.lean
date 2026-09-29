-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq
-- name    : WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver.exists_comp_fst_schemeKer_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/d3c0bf3c-3238-541f-ae9f-edbf706cffd7
-- title:
--   A relative Drinfeld basis consists of q-torsion points
-- statement:
--   Let $R$ be a commutative ring and $V$ a projective Weierstrass curve over $R$, and write $\mathtt{projModelStrCR}\ V$ for the structure morphism from the $\operatorname{Proj}$ of the graded quotient ring attached to $V$ to $\operatorname{Spec} R$. Let $G$ be a relative group law on this morphism, i.e. a functorial group structure on the sets $\mathrm{SchemeHomOver}\ t\ (\mathtt{projModelStrCR}\ V)$ of pairs $(\varphi, \varphi \circ (\mathtt{projModelStrCR}\ V) = t)$, compatible with base change along morphisms of test schemes. Let $q$ be a natural number with $2 \le q$, let $T$ be a scheme, $t : T \to \operatorname{Spec} R$, and let $P, Q$ be $T$-points of the projective model over $t$. Assume $G.\mathtt{IsDrinfeldBasisOver}\ q\ t\ P\ Q$, that is: the ideal sheaf datum on $\operatorname{Proj} \times_{\operatorname{Spec} R} T$ obtained as $\mathtt{prodKerGraph}$ of the family $G.\mathtt{basisTupleOver}\ q\ t\ P\ Q$ of $T$-points (indexed by $\mathrm{Fin}(q\cdot q)$) coincides with the ideal sheaf datum $G.\mathtt{torsionIdealOver}\ q\ t$, the pullback along the first projection of the kernel ideal sheaf of the first projection of the fibre product defining $G.\mathtt{schemeKer}\ q$. Then both $P$ and $Q$ factor through the $q$-torsion subscheme: there is $p : T \to G.\mathtt{schemeKer}\ q$, the fibre product of the $q$-fold multiplication morphism $G.\mathtt{schemeNsmul}\ q$ with the unit section $G.\mathtt{one}\ (\mathbb{1})$, such that $p$ followed by the first projection equals the underlying morphism of $P$, and likewise one for $Q$.
--
--   This is the elementary half of the comparison between Drinfeld level structures and naive level structures: a relative Drinfeld basis of level $q$ is in particular a pair of $q$-torsion sections. It is used in the representability and local-structure analysis of the moduli problems of level $\Gamma_0(p^n)$ and $\Gamma(p^n)$ type attached to the Weierstrass projective model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver.exists_comp_fst_schemeKer_eq
    {R : Type u} [CommRing R] {V : WeierstrassCurve.Projective R}
    (G : RelativeGroupLaw R (projModelStrCR V)) {q : ℕ} (hq : 2 ≤ q)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {P Q : SchemeHomOver t (projModelStrCR V)}
    (h : G.IsDrinfeldBasisOver q t P Q) :
    (∃ p : T ⟶ G.schemeKer q, p ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 = P.1) ∧
      ∃ p : T ⟶ G.schemeKer q, p ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 = Q.1 := by sorry
