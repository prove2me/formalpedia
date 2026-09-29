-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_map_fstHom_eq_one_and_smul_map_eq_map_map_of_nsmul_eq_one_of_nthSeries_eq_mul_X_pow
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_variableChange_map_fstHom_eq_one_and_smul_map_eq_map_map_of_nsmul_eq_one_of_nthSeries_eq_mul_X_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/aced460f-646b-5152-bb1f-eb74417a6440
-- title:
--   First-order Serre–Tate rigidity at an ordinary point
-- statement:
--   Fix a commutative ring $A$ and a family $\mathcal G$ of group laws, assigning to every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with $\Delta_W$ a unit a relative group law on the structure morphism `projModelStrCR W`; assume `𝒢.IsChordTangent` (for each such $T$, $W$, $\Delta_W$ there is an evaluation `ev` with `IsPointsEval W (𝒢 T W hΔ) ev`) and `𝒢.IsOriginIdentity` (for each such datum there is a ring homomorphism $\chi$ from `OriginChartRing W` to $T$ which is an origin-chart section of the identity element of the group law and kills `xOverY W` and `zOverY W`). Let $q$ be prime, $B$ an $A$-algebra, $V$ a Weierstrass curve over $B$ with $\Delta_V$ a unit, $k$ a field of characteristic $q$, and $\beta : B \to k[\varepsilon]$ a ring homomorphism into the dual numbers; write $\beta_0$ for $\beta$ followed by the projection $k[\varepsilon] \to k$. Suppose a formal group $F_0$ over $k$ has underlying two-variable power series the Weierstrass series `formalGroupLawFixed` of $V$ base-changed along $\beta_0$, and that its $q$-th iterate series `F₀.nthSeries q` (defined by $\;0$ at $0$ and by substituting the previous series and $X$ into $F_0$ at each step) equals $u \cdot X^q$ for some unit $u \in k\llbracket X \rrbracket$. Let $Q$ be a morphism to the projective model of $V$ over $\mathrm{Spec}\,\beta$, i.e. a scheme morphism whose composite with `projModelStrCR V` is `Spec.map β`, such that the $q$-fold iterate `nsmul` of $Q$ for the group law $\mathcal G(B,V)$ is the identity element, while the composite of $\mathrm{Spec}$ of the projection $k[\varepsilon] \to k$ with $Q$ differs from the identity element over $\mathrm{Spec}\,\beta_0$. The conclusion is that there exists a Weierstrass variable change $C$ over $k[\varepsilon]$ whose image under the projection $k[\varepsilon] \to k$ is the trivial change, and with $C \bullet (V \otimes_\beta k[\varepsilon])$ equal to the base change to $k[\varepsilon]$ of $V \otimes_{\beta_0} k$.
--
--   This is the first-order case of Serre–Tate local moduli: an ordinary elliptic curve over $k$ has no nontrivial first-order deformation carrying a $q$-torsion point with nonzero reduction, so the deformation is the constant one, witnessed by a variable change congruent to the identity modulo $\varepsilon$. It feeds the rigidity input for the Katz level-$q$ moduli packages, being used in the two statements producing $k[\varepsilon]$-algebra homomorphisms out of the level structures represented by `gamma0Pow` and `rigidDataH1Pow`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_map_fstHom_eq_one_and_smul_map_eq_map_map_of_nsmul_eq_one_of_nthSeries_eq_mul_X_pow.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_variableChange_map_fstHom_eq_one_and_smul_map_eq_map_map_of_nsmul_eq_one_of_nthSeries_eq_mul_X_pow
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (B : Type) [CommRing B] [Algebra A B] (V : WeierstrassCurve B) (hΔ : IsUnit V.Δ)
    (k : Type) [Field k] [CharP k q] (β : B →+* DualNumber k)
    (F₀ : FormalGroup k)
    (hF₀W : F₀.toPowerSeries = (V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).formalGroupLawFixed)
    (hF₀ : ∃ u : PowerSeries k, IsUnit u ∧ F₀.nthSeries q = u * PowerSeries.X ^ q)
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom β)) (projModelStrCR V))
    (hQq : (𝒢 B V hΔ).nsmul _ q Q = (𝒢 B V hΔ).one _)
    (hQ0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q.1 ≠
      ((𝒢 B V hΔ).one (Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)))).1) :
    ∃ C : WeierstrassCurve.VariableChange (DualNumber k),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 ∧
      C • V.map β = (V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).map (algebraMap k (DualNumber k)) := by sorry
