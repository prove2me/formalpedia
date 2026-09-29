-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_integral_veluQuotient_rescale_of_galois_stable
-- name    : WeierstrassCurve.exists_integral_veluQuotient_rescale_of_galois_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/c569c5bb-8065-5b1e-8f85-8acd4e85f984
-- title:
--   Integral rescaling of the Vélu quotient by a Galois-stable subgroup
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta(W)\neq 0$, let $p$ be a prime with $p\neq 2$, and let $Q$ be a point of the base change $W_{\bar{\mathbb{Q}}}$ of $W$ (first mapped to $\mathbb{Q}$ along $\mathbb{Z}\to\mathbb{Q}$, then to an algebraic closure $\bar{\mathbb{Q}}$) whose additive order is exactly $p$ and which satisfies: for every $\sigma\in\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ the point $\sigma\cdot Q$ lies in the subgroup of integer multiples of $Q$. Put $S$ for the finite subset of $\bar{\mathbb{Q}}\times\bar{\mathbb{Q}}$ consisting of the coordinate pairs of the points $k\cdot Q$ for $1\le k\le \lfloor p/2\rfloor$ (an affine point $(x,y)$ contributing $(x,y)$, the point at infinity contributing $(0,0)$). The assertion is that there exist a Weierstrass curve $W'$ over $\mathbb{Z}$ and a unit $u\in\bar{\mathbb{Q}}^{\times}$ such that $\Delta(W')\neq 0$, the base change of $W'$ to $\bar{\mathbb{Q}}$ equals the variable change $(u,0,0,0)$ applied to the Vélu quotient of $W_{\bar{\mathbb{Q}}}$ by $S$ — the curve with the same $a_1,a_2,a_3$ and with $a_4$ replaced by $a_4-5\sum_{P\in S}\mathrm{veluT}(P)$ and $a_6$ by $a_6-b_2\sum_{P\in S}\mathrm{veluT}(P)-7\sum_{P\in S}\mathrm{veluW}(P)$ — and moreover $u=p^{e}$ in $\bar{\mathbb{Q}}$ for some integer $e$.
--
--   This is the integral-model step in the construction of the quotient of an elliptic curve over $\mathbb{Q}$ by a Galois-stable subgroup of odd prime order, realised concretely through Vélu's formulae: after the quotient has been descended to $\mathbb{Q}$, a rescaling by a power of $p$ clears the denominators, which are supported at $p$ alone. It is used by [`WeierstrassCurve.exists_quotientDatum_of_galois_stable_primeCard`](thm.html#WeierstrassCurve.exists_quotientDatum_of_galois_stable_primeCard), which packages the quotient curve together with its integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_integral_veluQuotient_rescale_of_galois_stable.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_integral_veluQuotient_rescale_of_galois_stable
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p)
    (hQstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ • Q ∈ AddSubgroup.zmultiples Q) :
    let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
    let S := Wb.oddOrderSummingSet Q (p / 2)
    ∃ (W' : WeierstrassCurve ℤ) (u : (AlgebraicClosure ℚ)ˣ), W'.Δ ≠ 0 ∧
      (W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) =
        (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) • Wb.veluQuotient S ∧
      ∃ e : ℤ, (u : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ e := by sorry
