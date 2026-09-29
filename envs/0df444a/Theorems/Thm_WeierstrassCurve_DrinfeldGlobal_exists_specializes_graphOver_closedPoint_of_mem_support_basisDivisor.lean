-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/5d542e98-ebfe-5730-bf6e-70ce56fef0de
-- title:
--   Support of the basis divisor specialises to graph closed points
-- statement:
--   Let $T$ be a commutative ring which is local, let $W$ be a Weierstrass curve over $T$, and write $\mathrm{base} = \operatorname{Spec} T$ and $E \to \mathrm{base}$ for the structure morphism `projModelStrCR W` of the projective model of $W$, presented as $\operatorname{Proj}$ of the quotient grading by the Weierstrass homogeneous ideal. Let $G$ be a relative group law on this morphism, that is, a family of multiplication, unit and inversion operations on $T'$-points $\{\varphi : T' \to E \mid \varphi \text{ lies over the given } T' \to \mathrm{base}\}$, functorial in $T'$ and satisfying the group axioms. Let $q \in \mathbb{N}$, let $P, Q$ be sections, i.e. morphisms $\mathrm{base} \to E$ over the identity of $\mathrm{base}$, and let $x$ be a point of the scheme $E \times_{\mathrm{base}} \mathrm{base}$ formed as the pullback of $E \to \mathrm{base}$ along $\mathrm{id}_{\mathrm{base}}$. Assume $x$ lies in the support of `basisDivisor G q P Q`, the product over $i \in \mathrm{Fin}(q \cdot q)$ of the kernel ideal sheaves of the graph morphisms of the sections $[i/q]P + [i \bmod q]Q$ (each $[a]P + [b]Q$ being $G$-multiplication of the $a$-fold and $b$-fold $G$-multiples of $P$ and of $Q$). Then there exist $a, b \in \mathbb{N}$ with $a < q$, $b < q$ such that $x$ specialises to the image, under the underlying continuous map of the graph morphism $\mathrm{base} \to E \times_{\mathrm{base}} \mathrm{base}$ of the section $[a]P + [b]Q$, of the closed point of $T$.
--
--   This is the topological reduction step for the Drinfeld-style divisor $\sum_{a,b<q} [\,aP+bQ\,]$ on the projective model over a local base: its support meets only the closed-point fibres of the finitely many graphs involved. It is used by [`WeierstrassCurve.DrinfeldGlobal.torsionIdeal_le_basisDivisor_of_nsmul_eq_one_of_nthSeries_eq_mul_prod`](thm.html#WeierstrassCurve.DrinfeldGlobal.torsionIdeal_le_basisDivisor_of_nsmul_eq_one_of_nthSeries_eq_mul_prod) to reduce an inclusion of ideal sheaves to comparisons of germs at finitely many closed points, one for each pair $(a,b)$ with $a,b<q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor
    {T : Type} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve T)
    (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W)
    (x : ↥(pullback (projModelStrCR W) (𝟙 (base (T := T)))))
    (hx : x ∈ ((basisDivisor G q P Q).support : Set ↥(pullback (projModelStrCR W) (𝟙 (base (T := T)))))) :
    ∃ a b : ℕ, a < q ∧ b < q ∧
      x ⤳ (graphOver (projModelStrCR W) (linComb G P Q a b).1 (linComb G P Q a b).2).base
        (IsLocalRing.closedPoint T) := by sorry
