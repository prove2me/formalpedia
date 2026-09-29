-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_map_eq_smul_one_of_zlinComb_eq_zsmulSection
-- name    : WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.map_eq_smul_one_of_zlinComb_eq_zsmulSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/8183d635-d5cf-5ffd-94b0-63cd289a6c3d
-- title:
--   Relabellings fixing a Drinfeld q-basis up to sign are ≡ ε · 1
-- statement:
--   Let $K$ be a field and $W$ a projective Weierstrass curve over $K$ whose discriminant $W.\Delta$ is a unit. Let $G$ be a relative group law on the structure morphism $\mathrm{Proj}$ of the graded ring of $W$ over $\operatorname{Spec} K$, that is, a fibrewise-natural system of multiplication, unit and inverse operations on the sets $\{\varphi : T \to \mathrm{Proj} \mid \varphi \text{ over } t\}$ of $T$-points over $\operatorname{Spec} K$ satisfying the group axioms. Let $ev$ be a family of bijections, for every field extension $F$ of $K$, between the $\operatorname{Spec} F$-points of this model over $\operatorname{Spec} K$ and the affine points of $W$ base-changed to $F$, and assume `IsPointsEval`: each $ev_F$ takes $G$-multiplication to addition of points and commutes with the Galois twist by any $K$-algebra automorphism $\sigma$ of $F$. Let $q$ be a natural number with $q \neq 0$ in $K$, and let $P, Q$ be sections of the model over $\operatorname{Spec} K$ such that `IsDrinfeldBasis G q P Q` holds, i.e. the ideal sheaf data `basisDivisor G q P Q`, cut out by the tuple of sections $aP + bQ$ for $a,b < q$, coincides with `torsionIdeal G q`, the kernel of the $q$-fold multiplication map composed with the unit section. Let $g$ be a $2 \times 2$ integer matrix and $\varepsilon = \pm 1$, and suppose that $g_{00}P + g_{10}Q = \varepsilon P$ and $g_{01}P + g_{11}Q = \varepsilon Q$, where integer multiples and sums are formed with $G$ (via `zsmulSection` and `zlinComb`). Then the entrywise reduction of $g$ modulo $q$ equals $\varepsilon$ times the identity matrix in $M_2(\mathbb{Z}/q)$.
--
--   Over a field in which $q$ is invertible a Drinfeld basis of level $q$ is a genuine basis of the $q$-torsion, so a matrix relabelling that sends the pair $(P,Q)$ to $(\varepsilon P, \varepsilon Q)$ must be congruent to $\varepsilon \cdot 1$ modulo $q$ (Katz–Mazur 1.5.1). It supplies the Drinfeld-level-structure component in the analysis of points of the full level-$q$ moduli problem fixed by a relabelling automorphism, and is used by the results on `RawDrinfeldPair.IsLevel`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_map_eq_smul_one_of_zlinComb_eq_zsmulSection.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.map_eq_smul_one_of_zlinComb_eq_zsmulSection
    {K : Type} [Field K] (W : WeierstrassCurve.Projective K) (hΔ : IsUnit W.Δ)
    (G : RelativeGroupLaw K (projModelStrCR W))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W) ≃ (W.baseChange F).toAffine.Point)
    (hev : IsPointsEval W G ev)
    (q : ℕ) (hqK : (q : K) ≠ 0) (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hP : ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0) = ModularCurve.LevelRelabelling.zsmulSection G ε P)
    (hQ : ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1) = ModularCurve.LevelRelabelling.zsmulSection G ε Q) :
    g.map (Int.castRingHom (ZMod q)) = (ε : ZMod q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by sorry
