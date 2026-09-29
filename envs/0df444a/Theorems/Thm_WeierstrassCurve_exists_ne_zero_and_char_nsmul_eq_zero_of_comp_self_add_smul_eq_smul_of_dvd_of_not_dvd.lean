-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd
-- name    : WeierstrassCurve.exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/2bb50ff6-a139-5522-aa8b-e8d5fdc61ec1
-- title:
--   Deuring's criterion: endomorphism with p ∣ q, p ∤ t forces ordinarity
-- statement:
--   Let $k$ be an algebraically closed field of prime characteristic $p$, and let $W$ be a Weierstrass curve over $k$ which is elliptic. Let $\beta$ be an endomorphism of the additive group $W(k)$ of points of the associated affine curve (the affine solutions of the Weierstrass equation together with the point at infinity, which is the zero element) lying in [`WeierstrassCurve.rationalHomSet k W W`](def/WeierstrassCurve_RationalEnd.html#L28); that is, either $\beta = 0$, or $\beta$ is rationally represented: there are bivariate polynomials $nX, dX, nY, dY$ over $k$ and a finite set $B \subseteq k$ such that for every nonsingular point $(x,y)$ with $x \notin B$ the evaluations of $dX$ and $dY$ at $(x,y)$ are nonzero and $\beta$ sends $(x,y)$ to the point with coordinates $(nX/dX, nY/dY)$ evaluated at $(x,y)$. Let $t, q$ be integers such that $\beta \circ \beta + q \cdot \mathrm{id} = t \cdot \beta$ as endomorphisms of $W(k)$, such that $m^2 - tm + q \neq 0$ for every integer $m$, such that $p \mid q$ and such that $p \nmid t$. Then there exists a point $T \in W(k)$ with $T \neq 0$ and $p \cdot T = 0$.
--
--   This is Deuring's criterion in the form: an elliptic curve in characteristic $p$ admitting a rational endomorphism whose quadratic relation has norm divisible by $p$ and trace prime to $p$, and whose characteristic polynomial has no integer root, is ordinary, i.e. has a nonzero $p$-torsion point. It is used in the Čeredník–Drinfeld part of the development, in the identification of kernel ideals and of the image of the Frobenius under the rational point homomorphism, and in a statement about variable changes in characteristic $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) [W.IsElliptic] {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W) (t q : ℤ) (hchar : β.comp β + q • AddMonoidHom.id _ = t • β) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) (hq : (p : ℤ) ∣ q) (ht : ¬ (p : ℤ) ∣ t) : ∃ T : W.toAffine.Point, T ≠ 0 ∧ p • T = 0 := by sorry
