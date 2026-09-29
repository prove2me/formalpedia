-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j
-- name    : WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/54c20758-865b-57d0-abc6-27d7fcfee665
-- title:
--   Non-integral j forces endomorphisms to be integer multiplications
-- statement:
--   Let $F$ be an algebraically closed field of characteristic zero and let $W$ be a Weierstrass curve over $F$ which is elliptic. The affine curve $W^{\mathrm{aff}} = W.\mathtt{toAffine}$ is assumed to carry three structures: a `GenusOnePlaceGate`, i.e. a bijection between the group $W^{\mathrm{aff}}(F)$ of points and the places of the function field $F(W)$ over $F$, together with the assertion that every such place has degree $1$; the centring condition `GenusOnePlaceGate.IsCentred`, i.e. for each nonsingular point $(x,y)$ the images in $F(W)$ of the coordinate-ring classes of $X-x$ and of $Y-y$ lie in the non-units of the valuation subring of the place attached to that point; and `AbelTheorem`, i.e. a divisor of degree $0$ is principal if and only if its point-sum vanishes. It is further assumed that for every isogeny endomorphism datum $D$ of $W^{\mathrm{aff}}$ — an $F$-algebra endomorphism $\iota$ of $F(W)$ whose underlying ring map is integral, with $F(W)$ finite as a module over itself along $\iota$ — the pushforward norm formula holds along $\iota$: whenever $f \in F(W)$ is nonzero and a divisor has $\mathrm{ord}_w f$ at every place $w$, its pushforward has value $\mathrm{ord}_v(\mathrm{Norm}\, f)$ at every place $v$. Finally, assume $W.j$ is not integral over $\mathbb{Z}$, and let $D_0$ be an isogeny endomorphism datum. Then there is an integer $m$ such that the additive endomorphism $D_0.\mathtt{pointEnd}$ of $W^{\mathrm{aff}}(F)$ — obtained by transporting divisor-class pushforward along $D_0.\iota$ through the identification of points with degree-zero divisor classes — satisfies $D_0.\mathtt{pointEnd}(P) = m \cdot P$ for all points $P$.
--
--   This is the statement that an elliptic curve whose $j$-invariant is not an algebraic integer admits no complex multiplication, $\mathrm{End}(E) = \mathbb{Z}$, in the form appropriate to the project's divisor-theoretic model of isogeny endomorphisms. It is used in the study of the diagonal modular polynomials $\Phi_N(X,X)$, where separability and root-surjectivity arguments require that curves with non-integral $j$ have only the integer endomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine] [AbelTheorem W.toAffine]
    (hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong F D.ι D.hfin)
    (hj : ¬ _root_.IsIntegral ℤ W.j) (D₀ : IsogenyEndDatum W.toAffine) :
    ∃ m : ℤ, ∀ P : W.toAffine.Point, D₀.pointEnd (hNs D₀) P = m • P := by sorry
