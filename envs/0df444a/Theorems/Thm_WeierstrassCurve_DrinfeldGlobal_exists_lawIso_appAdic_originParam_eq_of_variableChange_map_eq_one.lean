-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/e2ef32c6-bd89-56fe-a8b7-bedf5b8c0b60
-- title:
--   Transport of a law isomorphism along a trivial variable change
-- statement:
--   Let $T$ be a local ring (in universe $u$) which is adically complete for its maximal ideal, let $k$ be a field, and let $\mathrm{res}_T : T \to k$ be a surjective ring homomorphism whose kernel is $\mathfrak m_T$. Let $W$ be a Weierstrass curve over $T$, let $C$ be a variable change over $T$ with $C.\mathrm{map}\ \mathrm{res}_T = 1$, and put $W' = C \bullet W$. Let $\varphi : \mathrm{projModelGradingCR}\ W \to \mathrm{projModelGradingCR}\ (C \bullet W)$ be a graded ring homomorphism whose image pulls back the irrelevant ideal (so that $\mathrm{Proj.map}\ \varphi$ is defined), and assume `IsVariableChangeHom W C φ`: $\varphi$ fixes the classes of constants and sends the classes of $X_0, X_1, X_2$ to $u^2X_0 + rX_2$, $u^3X_1 + u^2sX_0 + tX_2$ and $X_2$ respectively. Let $P, Q$ be sections of the projective model of $W$ (morphisms over the base) and $\chi_P, \chi_Q$ ring homomorphisms from the origin chart ring of $W$ (the degree-zero localisation away from the coordinate $\mathrm{coord}\ W\ 1$) to $T$ such that each $\chi$ is the origin chart of its section and both $\mathrm{originParam}\ \chi = -\chi(\mathrm{xOverY}\ W)$ and $\mathrm{originW}\ \chi$ lie in $\mathfrak m_T$; likewise $P', Q'$, $\chi_{P'}, \chi_{Q'}$ for $W'$, with the compatibilities that $P'$, resp. $Q'$, followed by the transport along $W' = C \bullet W$ and by $\mathrm{Proj.map}\ \varphi$ equals $P$, resp. $Q$. Let $F'$ and $G_T$ be formal groups over $T$ whose underlying power series are $W.\mathrm{formalGroupLawFixed}$ and $W'.\mathrm{formalGroupLawFixed}$, let $G$ be a formal group over $T$, and let $\psi : G_T \to G$ be a law isomorphism (a power series with zero constant term intertwining the two laws, with unit linear coefficient) whose coefficients satisfy $\mathrm{res}_T(\mathrm{coeff}_n \psi) = \delta_{n,1}$. Finally let $y_0, y_1 \in T$ be the $\mathfrak m_T$-adic evaluations of $\psi$ at $\mathrm{originParam}\ \chi_{P'}$ and $\mathrm{originParam}\ \chi_{Q'}$. Then there exists a law isomorphism $\psi' : F' \to G$ with $\mathrm{res}_T(\mathrm{coeff}_n \psi') = \delta_{n,1}$ for all $n$ and with $\mathfrak m_T$-adic evaluations $\psi'(\mathrm{originParam}\ \chi_P) = y_0$ and $\psi'(\mathrm{originParam}\ \chi_Q) = y_1$.
--
--   This is the formal-group bookkeeping needed to make a pair of marked points on a Weierstrass curve, together with a parametrisation of its formal group, independent of the Weierstrass model chosen within a variable change that is trivial modulo the maximal ideal. It is used in the construction of algebra homomorphisms out of the level-structure moduli packages, where a rigidified Weierstrass datum must be compared with the given one after such a variable change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    {k : Type u} [Field k] (resT : T →+* k) (hsT : Function.Surjective resT) (hkT : RingHom.ker resT = maximalIdeal T)
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) (hC1 : C.map resT = 1)
    (W' : WeierstrassCurve T) (hW' : W' = C • W)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hvc : IsVariableChangeHom W C φ)
    (P Q : Section W) (χP χQ : OriginChartRing W →+* T)
    (hP : ReducesToOrigin P χP (maximalIdeal T)) (hQ : ReducesToOrigin Q χQ (maximalIdeal T))
    (P' Q' : Section W') (χP' χQ' : OriginChartRing W' →+* T)
    (hP' : ReducesToOrigin P' χP' (maximalIdeal T)) (hQ' : ReducesToOrigin Q' χQ' (maximalIdeal T))
    (hPP' : P'.1 ≫ eqToHom (congrArg projModelCR hW') ≫ Proj.map φ hφ = P.1)
    (hQQ' : Q'.1 ≫ eqToHom (congrArg projModelCR hW') ≫ Proj.map φ hφ = Q.1)
    (F' : FormalGroup T) (hF' : F'.toPowerSeries = W.formalGroupLawFixed)
    (GT : FormalGroup T) (hGT : GT.toPowerSeries = W'.formalGroupLawFixed)
    (G : FormalGroup T) (ψ : FormalGroup.LawIso GT G)
    (hψ : ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0)
    (y₀ y₁ : T)
    (hy₀ : ψ.toLawHom.appAdic (maximalIdeal T) (originParam χP') = y₀)
    (hy₁ : ψ.toLawHom.appAdic (maximalIdeal T) (originParam χQ') = y₁) :
    ∃ ψ' : FormalGroup.LawIso F' G,
      (∀ n : ℕ, resT (PowerSeries.coeff n ψ'.series) = if n = 1 then 1 else 0) ∧
      ψ'.toLawHom.appAdic (maximalIdeal T) (originParam χP) = y₀ ∧
      ψ'.toLawHom.appAdic (maximalIdeal T) (originParam χQ) = y₁ := by sorry
