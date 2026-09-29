-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq
-- name    : WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/93fd7e0a-3705-57ba-bebe-bf48e6f46962
-- title:
--   Degree-N endomorphism forces Φ_N(j(E),j(E))=0
-- statement:
--   Let $K$ be a field in universe $u$, equipped with decidable equality, algebraically closed and of characteristic $0$, and let $W$ be a Weierstrass curve over $K$ which is elliptic. Let $N$ be a natural number with `NeZero N` which is squarefree, and let `data` be a [`ModularCurve.ModularPolynomialData N`](def/ModularCurve_X0.html#L215): a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ that is monic, whose degree in $Y$ equals $\sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which vanishes when its coefficients are evaluated through the ring homomorphism $\mathbb{Z}[X] \to \mathrm{LaurentSeries}\,\mathbb{Q}$ sending $X$ to the $q$-expansion of $j$ and $Y$ is sent to the Laurent series `jqN N`. Let $D$ be an `IsogenyEndDatum` for the affine model of $W$, that is: a $K$-algebra endomorphism $\iota = D.\iota$ of the function field $K(W)$, integral as a ring homomorphism, and such that $K(W)$ is a finite module over itself via $\iota$; assume moreover that this module has rank exactly $N$, i.e. $\operatorname{finrankAlong} K\, D.\iota = N$. The conclusion is that the diagonal polynomial $\Phi(X,X) \in \mathbb{Z}[X]$, obtained from $\Phi$ by substituting $X$ for the outer variable with coefficients mapped by the identity of $\mathbb{Z}[X]$, vanishes when evaluated at $j(W) \in K$.
--
--   This is the classical assertion that an elliptic curve carrying a self-isogeny of degree $N$ (here presented field-theoretically, as a finite integral self-embedding of the function field of index $N$) yields a point of $X_0(N)$ lying over $(j(E),j(E))$, so that $j(E)$ is a root of the diagonal modular polynomial $\Phi_N(X,X)$. It is used to rule out endomorphisms of degree $N>1$ when $j(W)$ is transcendental or non-integral, in [`WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j`](thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j) and [`WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j`](thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {N : ℕ} [NeZero N] (hN : Squarefree N) (data : ModularCurve.ModularPolynomialData N)
    (D : IsogenyEndDatum W.toAffine) (hdeg : finrankAlong K D.ι = N) :
    Polynomial.aeval W.j (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X) = 0 := by sorry
