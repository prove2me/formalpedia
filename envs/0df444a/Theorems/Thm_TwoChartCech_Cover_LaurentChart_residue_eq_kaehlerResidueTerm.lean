-- Prove2me | Theorems.Thm_TwoChartCech_Cover_LaurentChart_residue_eq_kaehlerResidueTerm
-- name    : TwoChartCech.Cover.LaurentChart.residue_eq_kaehlerResidueTerm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/1193e488-fa95-544d-8333-584df22ca865
-- title:
--   Laurent-chart residue equals the Kähler residue term at v
-- statement:
--   Let $k$ be a field and $F$ a field extension of $k$ equipped with canonical local residue data in the strong sense (`HasCanonicalLocalResidueKStar`: a chosen datum at every place $v$ of $F/k$, whose residue map $\mathrm{res}_v\colon F \to \kappa(v)$ kills $(\pi_v^{n+1})^{-1}$ for all $n \ge 1$), and let $\mathcal U$ be a two-chart cover over $k$, i.e. $k$-algebras $A_0, A_1, A_{01}$ together with $k$-algebra maps $\rho_0\colon A_0 \to A_{01}$ and $\rho_1\colon A_1 \to A_{01}$. Fix a Laurent chart $\Lambda$ on $\mathcal U$, that is a ring homomorphism $\Lambda^{\mathrm{e}}\colon A_{01} \to k((t))$ carrying $\mathrm{algebraMap}\,r$ to the constant series $C(r)$; a $k$-algebra map $\psi\colon A_{01} \to F$; and a $k$-linear $\Phi\colon \Omega_{A_{01}/k} \to \Omega_{F/k}$ with $\Phi(s \cdot dg) = \psi(s)\cdot d(\psi g)$ for all $s, g \in A_{01}$. Assume given a ring homomorphism $\Lambda'\colon F \to k((t))$ with $\Lambda'(\psi y) = \Lambda^{\mathrm{e}}(y)$ for all $y \in A_{01}$, and a place $v$ of $F/k$ (a valuation subring $\mathcal O_v \ne F$ of $F$ containing $k$ and a principal ideal ring) such that $d\pi_v$ spans $\Omega_{F/k}$ over $F$, with $\Omega_{F/k}$ nontrivial, and such that $\mathcal O_v$ is exactly the power-series locus of $\Lambda'$: $f \in \mathcal O_v$ if and only if $\Lambda'(f)$ lies in the image of $k[[t]] \to k((t))$. Assume finally that the chart parameter is realised by a function: $\Lambda'(t_0) = t$ for some $t_0 \in F$. Then for every $\eta \in \Omega_{A_{01}/k}$ the chart residue $\Lambda.\mathrm{residue}\,\eta$, the coefficient of $t^{-1}$ of the image of $\eta$ under the $A_{01}$-linear map extending $g \mapsto \tfrac{d}{dt}\Lambda^{\mathrm{e}}(g)$, equals $\mathrm{kaehlerResidueTerm}$ of $\Phi\eta$ at $v$ against the constant family with value $1$, namely $\mathrm{Tr}_{\kappa(v)/k}\bigl(\mathrm{res}_v(1 \cdot \partial_v(\Phi\eta))\bigr)$, where $\partial_v$ is the coefficient of a differential with respect to $d\pi_v$.
--
--   This identifies the formal residue read off from a Laurent expansion on the overlap chart with the intrinsically defined residue at the place whose valuation ring is that chart's power-series locus, in the case where the place has residue field $k$ and the chart parameter comes from a global function. It supplies the per-chart comparison used by [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter) and by the comparison of the integral pairing with the Serre pairing in [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_Cover_LaurentChart_residue_eq_kaehlerResidueTerm.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicCurve_LocalResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem TwoChartCech.Cover.LaurentChart.residue_eq_kaehlerResidueTerm {k : Type u} [Field k] {F : Type v} [Field F] [Algebra k F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar k F]
    {𝒰 : TwoChartCech.Cover.{u, w} k} (Λ : 𝒰.LaurentChart) (ψ : 𝒰.A01 →ₐ[k] F)
    (Φ : Ω[𝒰.A01⁄k] →ₗ[k] Ω[F⁄k])
    (hΦ : ∀ s g : 𝒰.A01, Φ (s • KaehlerDifferential.D k 𝒰.A01 g) = ψ s • KaehlerDifferential.D k F (ψ g))
    (Λ' : F →+* LaurentSeries k) (hΛ' : ∀ y : 𝒰.A01, Λ' (ψ y) = Λ.expand y)
    (v : AlgebraicCurve.Place k F) [v.DCoordGenerates] [Nontrivial Ω[F⁄k]]
    (hΛv : ∀ f : F, f ∈ v.toValuationSubring ↔ Λ' f ∈ (HahnSeries.ofPowerSeries ℤ k).range)
    {t₀ : F} (ht₀ : Λ' t₀ = HahnSeries.single 1 1) (η : Ω[𝒰.A01⁄k]) :
    Λ.residue η = AlgebraicCurve.kaehlerResidueTerm (Φ η) (AlgebraicCurve.diagonalHom k F 1) v := by sorry
