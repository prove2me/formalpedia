-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow
-- name    : WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/9a9a3d48-0360-5d76-9dae-6268a3136b29
-- title:
--   Chart-wise q-power map followed by coefficient projection is absolute Frobenius
-- statement:
--   Let $q$ be a prime, $T$ a commutative ring of characteristic $q$, and $W$ a Weierstrass curve over $T$; write $E_W$ for `projModelCR W.toProjective`, the $\operatorname{Proj}$ of the graded quotient of the polynomial ring in three variables by the homogeneous Weierstrass ideal, and $W^{(q)} =$ `W.map (frobenius T q)` for the curve obtained by raising the coefficients of $W$ to the $q$-th power. Let $\Phi : E_W \to E_{W^{(q)}}$ be a morphism of schemes with $\Phi$ followed by the structure morphism of $E_{W^{(q)}}$ to $\operatorname{Spec} T$ equal to that of $E_W$ (so $\Phi$ is a $T$-morphism). Assume, on the chart $D_+(Z)$, that there is a ring homomorphism $\psi$ from the degree-zero homogeneous localisation `ZChartRing` of $W^{(q)}$ at the class of $Z$ to that of $W$ carrying $X/Z$ and $Y/Z$ to the $q$-th powers of $X/Z$ and $Y/Z$ and with $\Phi$ precomposed by the chart inclusion of $E_W$ equal to $\operatorname{Spec}(\psi)$ followed by the chart inclusion of $E_{W^{(q)}}$; and analogously on the chart $D_+(Y)$, with `OriginChartRing` and the coordinates $X/Y$, $Z/Y$. Let $\varphi$ be a graded ring homomorphism from the graded coordinate ring of $E_W$ to that of $E_{W^{(q)}}$ whose induced map satisfies the condition `hφ` that the irrelevant ideal of the target lies in the image of the irrelevant ideal of the source, so that $\operatorname{Proj}(\varphi) : E_{W^{(q)}} \to E_W$ is defined, and assume `IsCoefficientHom`: $\varphi$ sends the class of a constant $C(a)$ to the class of $C(a^q)$ and fixes the classes of the three coordinates. Assume finally $q = 0$ in $\Gamma(E_W, \mathcal O)$. Then $\Phi$ followed by $\operatorname{Proj}(\varphi)$ equals the absolute Frobenius `frobenius q 1` of $E_W$, the identity on the underlying space together with the $q$-th power map on sections.
--
--   This identifies the composite of a chart-wise $q$-power $T$-morphism $E_W \to E_{W^{(q)}}$ with the coefficient projection $E_{W^{(q)}} \to E_W$ as the absolute $q$-Frobenius of the projective Weierstrass model, the usual factorisation of absolute Frobenius through the Frobenius twist. It is the geometric half of the statement that such a $\Phi$ is compatible with the group law, used in [`WeierstrassCurve.DrinfeldGlobal.comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow`](thm.html#WeierstrassCurve.DrinfeldGlobal.comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassProjModel NeronModelInfra
  WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [CharP T q]
    (W : WeierstrassCurve T)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map (frobenius T q)).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (frobenius T q)).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : IsCoefficientHom W.toProjective (frobenius T q) φ)
    (hE : (q : Γ(projModelCR W.toProjective, ⊤)) = 0) :
    Φ ≫ Proj.map φ hφ = (projModelCR W.toProjective).frobenius q 1 Fact.out hE := by sorry
