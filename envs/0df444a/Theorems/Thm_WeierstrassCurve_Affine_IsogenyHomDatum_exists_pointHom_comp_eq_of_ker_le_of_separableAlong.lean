-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_IsogenyHomDatum_exists_pointHom_comp_eq_of_ker_le_of_separableAlong
-- name    : WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_separableAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/ed334616-4756-5266-b15d-59f72afad74a
-- title:
--   Separable isogenies factor through maps with smaller kernel
-- statement:
--   Let $F$ be an algebraically closed field with decidable equality, and let $V_0,V_1,V_2$ be affine Weierstrass curves over $F$, each elliptic, each equipped with a place gate (a bijection `pointEquivPlace` between its group of points and the places of its function field over $F$, all places having degree $1$) and satisfying the Abel theorem (a degree-zero divisor is principal exactly when its image under `divisorSum` vanishes), the gate on $V_0$ being moreover centred (for every nonsingular affine point the classes of $X$ and of $Y-y$ lie in the non-units of the valuation subring of the associated place). Let $\varphi$ be an isogeny datum from $V_0$ to $V_1$, that is an $F$-algebra map $\varphi.\iota : F(V_1) \to F(V_0)$ which is integral and along which $F(V_0)$ is a finite $F(V_1)$-module, and assume $F(V_0)$ is separable over $F(V_1)$ along $\varphi.\iota$ and that the pushforward norm formula holds along $\varphi.\iota$ (the pushforward of the divisor of any nonzero $f \in F(V_0)$ has $v$-coefficient $\operatorname{ord}_v$ of the norm of $f$). Let $\psi$ be such a datum from $V_0$ to $V_2$ with the same two properties. Assume every $P \in V_0(F)$ killed by the induced homomorphism $\varphi.\mathrm{pointHom} : V_0(F) \to V_1(F)$ is killed by $\psi.\mathrm{pointHom}$. Then there exist an isogeny datum $\chi$ from $V_1$ to $V_2$, a proof that $F(V_1)$ is separable over $F(V_2)$ along $\chi.\iota$, and a proof of the pushforward norm formula along $\chi.\iota$, such that $\chi.\iota$ followed by $\varphi.\iota$ equals $\psi.\iota$ as maps $F(V_2) \to F(V_0)$, and such that $\chi.\mathrm{pointHom}(\varphi.\mathrm{pointHom}(P)) = \psi.\mathrm{pointHom}(P)$ for all $P \in V_0(F)$.
--
--   This is the factorisation criterion for isogenies in the form of Silverman, Corollary III.4.11: an isogeny whose kernel contains the kernel of another factors through it, here in the separable setting over an arbitrary algebraically closed base field, with the factorisation recorded both on function fields and on points. It is used to produce the isomorphism comparing two isogenies with equal kernel and equal degree, and in the construction of quotients by finite subgroups via variable changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_IsogenyHomDatum_exists_pointHom_comp_eq_of_ker_le_of_separableAlong.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve AlgebraicCurve
open WeierstrassCurve.Affine

universe u

theorem WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_separableAlong
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {V₀ V₁ V₂ : WeierstrassCurve.Affine F} [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
    [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁] [V₂.IsElliptic] [GenusOnePlaceGate V₂] [AbelTheorem V₂]
    [GenusOnePlaceGate.IsCentred V₀]
    (φ : IsogenyHomDatum V₀ V₁) (hsepφ : SeparableAlong F φ.ι) (hNφ : NormFormulaAlong F φ.ι φ.hfin)
    (ψ : IsogenyHomDatum V₀ V₂) (hsepψ : SeparableAlong F ψ.ι) (hNψ : NormFormulaAlong F ψ.ι ψ.hfin)
    (hker : ∀ P : V₀.Point, φ.pointHom hNφ P = 0 → ψ.pointHom hNψ P = 0) :
    ∃ (χ : IsogenyHomDatum V₁ V₂) (hsepχ : SeparableAlong F χ.ι) (hNχ : NormFormulaAlong F χ.ι χ.hfin),
      φ.ι.comp χ.ι = ψ.ι ∧
      ∀ P : V₀.Point, χ.pointHom hNχ (φ.pointHom hNφ P) = ψ.pointHom hNψ P := by sorry
