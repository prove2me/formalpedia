-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj
-- name    : WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/fe570829-e244-5187-8446-8c5a3061e4ea
-- title:
--   Drinfeld Γ(q)-basis criterion over a field, q invertible
-- statement:
--   Let $K$ be a field, let $W$ be a projective Weierstrass cubic over $K$ whose discriminant $W.\Delta$ is a unit, and write $E \to \operatorname{Spec} K$ for the associated model `projModelStrCR W`, the composite of $\mathrm{Proj}$ of the graded quotient ring of $W$ to $\operatorname{Spec}$ of its degree-zero part with the structure morphism. Let $G$ be a relative group law on this model, i.e. a functorial group structure (multiplication, unit, inverse, associativity, unit laws, left inverse, and naturality of multiplication under base change of the test scheme) on the sets $\{\varphi : T \to E \mid \varphi \text{ followed by } E \to \operatorname{Spec} K \text{ equals } t\}$ for all $t : T \to \operatorname{Spec} K$. Let $ev$ assign to every field $F$ that is a $K$-algebra a bijection between the $F$-points of the model over $\operatorname{Spec}$ of $\operatorname{Spec}(K \to F)$ and the Mordell–Weil group of the affine curve $W \otimes_K F$, and assume `IsPointsEval W G ev`: each $ev_F$ carries $G$-multiplication to addition of points and intertwines the Galois twist by any $\sigma \in \mathrm{Aut}_K(F)$ with the map on points induced by $\sigma$. Let $q$ be a natural number with $q \neq 0$ in $K$, and let $P, Q$ be sections of $E$ over the identity of $\operatorname{Spec} K$ satisfying $[q]P = [q]Q = O$ for $G$, and such that the map $(a,b) \mapsto \mathrm{linComb}\,G\,P\,Q\,a\,b = [a]P + [b]Q$ is injective on pairs with $a, b < q$. Then `IsDrinfeldBasis G q P Q` holds: on the pullback of $E$ along the identity of $\operatorname{Spec} K$, the ideal sheaf datum `basisDivisor G q P Q`, obtained by `prodKerGraph` from the tuple `basisTuple G q P Q` of these $q^2$ sections, coincides with `torsionIdeal G q`, the kernel ideal sheaf datum of the first projection out of the pullback of `G.schemeNsmul q` against the unit section, followed by `toPullbackId`.
--
--   This is the criterion, in the case where $q$ is invertible on the base, identifying a naive full level-$q$ structure given by two $q$-torsion sections with $q^2$ distinct integral combinations with a Drinfeld $\Gamma(q)$-basis in the sense of Katz–Mazur, i.e. with the statement that the divisor of the $q^2$ graphs equals the $q$-torsion subscheme. It is used to produce full level structures on Weierstrass models, for instance in the construction of points on the full level modular curve over a Laurent-series base and in the companion criterion phrased via sections through prescribed torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj
    {K : Type} [Field K] (W : WeierstrassCurve.Projective K) (hΔ : IsUnit W.Δ)
    (G : WeierstrassProjModel.RelativeGroupLaw K (WeierstrassProjModel.projModelStrCR W))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
          (WeierstrassProjModel.projModelStrCR W) ≃ (W.baseChange F).toAffine.Point)
    (hev : WeierstrassProjModel.IsPointsEval W G ev)
    (q : ℕ) (hqK : (q : K) ≠ 0)
    (P Q : WeierstrassCurve.DrinfeldGlobal.Section W)
    (hP : G.nsmul (𝟙 _) q P = G.one (𝟙 _)) (hQ : G.nsmul (𝟙 _) q Q = G.one (𝟙 _))
    (hinj : ∀ a b a' b' : ℕ, a < q → b < q → a' < q → b' < q →
      WeierstrassCurve.DrinfeldGlobal.linComb G P Q a b =
        WeierstrassCurve.DrinfeldGlobal.linComb G P Q a' b' → a = a' ∧ b = b') :
    WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis G q P Q := by sorry
