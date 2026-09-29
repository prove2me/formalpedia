-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det
-- name    : WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.zlinComb_zlinComb_of_isUnit_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/31d514e3-9ece-54ad-b21a-7058255a6096
-- title:
--   Relabelling a Drinfeld basis by a matrix with unit determinant mod q
-- statement:
--   Let $T$ be a commutative ring and $W$ a projective Weierstrass curve over $T$, with associated structure morphism `projModelStrCR W` from the Proj of its homogeneous coordinate ring to $\operatorname{Spec} T$; write `Section W` for the $T$-points of this model, i.e. morphisms from the base $\operatorname{Spec} T$ to it that compose with the structure morphism to give the identity. Let $G$ be a relative group law on `projModelStrCR W`, that is, a functorial multiplication, unit and inversion on the sets of points over arbitrary base schemes, subject to associativity, the unit laws, left inverses and compatibility with base change. Assume that the multiplication of $G$ is commutative on `Section W`. Let $q$ be a natural number and $P, Q$ two sections such that `IsDrinfeldBasis G q P Q` holds, i.e. the basis divisor `basisDivisor G q P Q` — the ideal sheaf data cut out by the product of the kernels of the graphs of the tuple of sections $aP + bQ$ — coincides with the $q$-torsion ideal `torsionIdeal G q`, the kernel of the morphism comparing multiplication by $q$ with the unit section. Let $g$ be a $2\times 2$ matrix over $\mathbb{Z}$ whose determinant becomes a unit in $\mathbb{Z}/q$. Then the two sections $g_{00}\cdot P + g_{10}\cdot Q$ and $g_{01}\cdot P + g_{11}\cdot Q$, formed by `zlinComb` from integer multiples taken with respect to $G$, again satisfy `IsDrinfeldBasis G q`.
--
--   This is the invariance of the Drinfeld $\Gamma(q)$-basis condition under the right action of $\mathrm{GL}_2(\mathbb{Z}/q)$ by relabelling of the pair of sections, in the sense of Katz–Mazur's notion of a full set of sections. It is used in the treatment of level structures of full level $q$, in particular in the lemmas identifying the determinant of a relabelling matrix from the induced action and in the analysis of diamond and level automorphisms on $\Gamma_0$- and $\Gamma_1$-type data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.zlinComb_zlinComb_of_isUnit_det
    {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hcomm : ∀ x y : Section W, G.mul _ x y = G.mul _ y x)
    (q : ℕ) (P Q : Section W) (h : IsDrinfeldBasis G q P Q)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod q)) :
    IsDrinfeldBasis G q
      (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0))
      (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1)) := by sorry
