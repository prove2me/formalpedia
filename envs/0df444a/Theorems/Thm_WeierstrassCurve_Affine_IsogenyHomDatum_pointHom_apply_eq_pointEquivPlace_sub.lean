-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_pointEquivPlace_sub
-- name    : WeierstrassCurve.Affine.IsogenyHomDatum.pointHom_apply_eq_pointEquivPlace_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/4a4032b7-541e-5445-977d-b8f3db36efb5
-- title:
--   Isogeny datum: induced map is place restriction minus origin
-- statement:
--   Let $F$ be an algebraically closed field and let $V_0,V_1$ be affine Weierstrass curves over $F$, both elliptic, each equipped with a `GenusOnePlaceGate` structure — a bijection `pointEquivPlace` between the points of the curve and the places of its function field over $F$, together with the assertion that every such place has degree $1$ — and each satisfying `AbelTheorem`, i.e. a divisor of degree $0$ is principal exactly when its divisor sum (its image in the group of points) vanishes. Let $\varphi$ be an `IsogenyHomDatum` from $V_0$ to $V_1$: an $F$-algebra map $\iota \colon F(V_1) \to F(V_0)$ which is integral and makes $F(V_0)$ a finite module over $F(V_1)$. Assume `NormFormulaAlong` for $\iota$: for every nonzero $f \in F(V_0)$ and every divisor $D$ on $V_0$ with $D(w) = \mathrm{ord}_w(f)$ for all $w$, the pushforward of $D$ along $\iota$ takes at each place $v$ of $F(V_1)$ the value $\mathrm{ord}_v(\mathrm{N}_{F(V_1)}(f))$. Then for every point $P$ of $V_0$, the value at $P$ of the additive map `pointHom` attached to these data equals $h(P) - h(O)$, where $h(Q)$ denotes the point of $V_1$ corresponding under `pointEquivPlace` to the restriction along $\iota$ of the place of $F(V_0)$ attached to $Q$, and $O$ is the zero point of $V_0$.
--
--   This is the comparison, in the style of "a morphism of elliptic curves is a translation composed with an isogeny", between the homomorphism on points induced by pushforward of divisor classes and the naive set-theoretic map given by restricting places along the function-field embedding: the two differ exactly by the constant $h(O)$, with no centring hypothesis on the datum. It is used in the analysis of kernels of such data, in the recognition of quotient isogenies up to isomorphism, and in the construction of variable changes identifying iterated quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_pointEquivPlace_sub.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.IsogenyHomDatum.pointHom_apply_eq_pointEquivPlace_sub
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {V₀ V₁ : WeierstrassCurve.Affine F} [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
    [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁]
    (φ : IsogenyHomDatum V₀ V₁) (hN : NormFormulaAlong F φ.ι φ.hfin) (P : V₀.Point) :
    φ.pointHom hN P
      = (pointEquivPlace (W := V₁)).symm ((placeOfPoint P).restrictAlong φ.ι φ.hι)
        - (pointEquivPlace (W := V₁)).symm ((placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι) := by sorry
