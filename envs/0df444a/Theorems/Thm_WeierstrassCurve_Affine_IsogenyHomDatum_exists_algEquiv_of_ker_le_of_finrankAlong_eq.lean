-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_IsogenyHomDatum_exists_algEquiv_of_ker_le_of_finrankAlong_eq
-- name    : WeierstrassCurve.Affine.IsogenyHomDatum.exists_algEquiv_of_ker_le_of_finrankAlong_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/415489d5-b9c0-51f7-8c70-d5c126c1eb40
-- title:
--   Equal-degree separable isogenies with nested kernels: isomorphic targets
-- statement:
--   Let $F$ be an algebraically closed field (no hypothesis on its characteristic) and let $V_0,V_1,V_2$ be affine Weierstrass curves over $F$, each elliptic and each equipped with a `GenusOnePlaceGate` structure (a bijection `pointEquivPlace` between its group of points and the places of its function field over $F$, all places having degree $1$, the place attached to a point being written `placeOfPoint`) and with `AbelTheorem` (for every divisor of degree $0$, principality is equivalent to the vanishing of its divisor sum); for $V_0$ the gate is moreover centred, i.e. at each affine point the classes of $X$ and of $Y$ lie in the nonunits of the corresponding valuation subring. Let $\varphi$ be an `IsogenyHomDatum` from $V_0$ to $V_1$, that is an $F$-algebra map $\varphi.\iota\colon F(V_1)\to F(V_0)$ which is integral and makes $F(V_0)$ a finite $F(V_1)$-module, and assume $F(V_0)/F(V_1)$ is separable along $\varphi.\iota$, that the pushforward norm formula for divisors holds along $\varphi.\iota$, and that restricting the place of $0\in V_0$ along $\varphi.\iota$ gives the place of $0\in V_1$; let $\psi$ be such a datum from $V_0$ to $V_2$ with the same three properties. Assume that every point of $V_0$ killed by the induced additive map `φ.pointHom` is killed by `ψ.pointHom`, and that the two function-field degrees $\operatorname{finrank}_{F(V_1)}F(V_0)$ and $\operatorname{finrank}_{F(V_2)}F(V_0)$ agree. Then there exist an $F$-algebra isomorphism $e\colon F(V_2)\to F(V_1)$, a proof that its underlying ring map is integral, and an additive map $g\colon V_1(F)\to V_2(F)$ such that $e$ followed by $\varphi.\iota$ equals $\psi.\iota$, such that $g\circ$`φ.pointHom`$=$`ψ.pointHom` on all points of $V_0$, and such that for every point $P_1$ of $V_1$ the restriction along $e$ of the place of $P_1$ is the place of $g(P_1)$.
--
--   This is the statement that a separable isogeny is determined, up to isomorphism of its target, by its kernel: comparable kernels together with equal degrees force the two targets to be isomorphic, compatibly with the point maps and with the place–point dictionaries (Silverman III.4.12). It is used in the construction of the quotient of an elliptic curve by a full torsion kernel, via [`WeierstrassCurve.exists_variableChange_eq_fullKernelQuotient_fullKernelQuotient_comp_eq_smul`](thm.html#WeierstrassCurve.exists_variableChange_eq_fullKernelQuotient_fullKernelQuotient_comp_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_IsogenyHomDatum_exists_algEquiv_of_ker_le_of_finrankAlong_eq.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve AlgebraicCurve
open WeierstrassCurve.Affine

universe u

theorem WeierstrassCurve.Affine.IsogenyHomDatum.exists_algEquiv_of_ker_le_of_finrankAlong_eq
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {V₀ V₁ V₂ : WeierstrassCurve.Affine F} [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
    [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁] [V₂.IsElliptic] [GenusOnePlaceGate V₂] [AbelTheorem V₂]
    [GenusOnePlaceGate.IsCentred V₀]
    (φ : IsogenyHomDatum V₀ V₁) (hsepφ : SeparableAlong F φ.ι) (hNφ : NormFormulaAlong F φ.ι φ.hfin)
    (hφ0 : (placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι = placeOfPoint (0 : V₁.Point))
    (ψ : IsogenyHomDatum V₀ V₂) (hsepψ : SeparableAlong F ψ.ι) (hNψ : NormFormulaAlong F ψ.ι ψ.hfin)
    (hψ0 : (placeOfPoint (0 : V₀.Point)).restrictAlong ψ.ι ψ.hι = placeOfPoint (0 : V₂.Point))
    (hker : ∀ P : V₀.Point, φ.pointHom hNφ P = 0 → ψ.pointHom hNψ P = 0)
    (hdeg : finrankAlong F φ.ι = finrankAlong F ψ.ι) :
    ∃ (e : V₂.FunctionField ≃ₐ[F] V₁.FunctionField) (he : e.toAlgHom.toRingHom.IsIntegral)
      (g : V₁.Point →+ V₂.Point),
      φ.ι.comp e.toAlgHom = ψ.ι ∧
      (∀ P : V₀.Point, g (φ.pointHom hNφ P) = ψ.pointHom hNψ P) ∧
      ∀ P₁ : V₁.Point, (placeOfPoint P₁).restrictAlong e.toAlgHom he = placeOfPoint (g P₁) := by sorry
