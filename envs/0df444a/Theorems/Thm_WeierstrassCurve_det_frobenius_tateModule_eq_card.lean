-- Prove2me | Theorems.Thm_WeierstrassCurve_det_frobenius_tateModule_eq_card
-- name    : WeierstrassCurve.det_frobenius_tateModule_eq_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/0ad0b44a-d9ea-57fb-9c02-ebf196794ea6
-- title:
--   Determinant of Frobenius on the ℓ-adic Tate module equals q
-- statement:
--   Let $F$ be a finite field, $q = \#F$, let $k$ be a field with decidable equality which is an algebraically closed $F$-algebra, and let $W$ be a Weierstrass curve over $F$ satisfying `W.IsElliptic`. Let $\sigma$ be an $F$-algebra automorphism of $k$ which acts as the $q$-power map, i.e. $\sigma x = x^{q}$ for every $x \in k$, and let $\ell$ be a prime with $(\ell : F) \neq 0$. Write $(W/k)$ for the base change of $W$ to $k$ and $(W/k).\mathrm{Point}$ for its group of affine points together with the point at infinity. The $\ell$-adic Tate module [`TateModule ℓ (W⁄k).Point`](def/EllipticCurve_TateModule.html#L15) is the additive subgroup of sequences $x : \mathbb{N} \to (W/k).\mathrm{Point}$ with $\ell^{n} \cdot x_n = 0$ and $\ell \cdot x_{n+1} = x_n$ for all $n$, a $\mathbb{Z}_\ell$-module, and [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) sends a group element to the endomorphism acting coordinatewise on such sequences. The assertion is that the determinant of the $\mathbb{Z}_\ell$-linear endomorphism of this Tate module attached to $\sigma$ equals the image of $q$ in $\mathbb{Z}_\ell$.
--
--   This is one half of the Hasse–Weil description of the characteristic polynomial $X^{2} - aX + q$ of the $q$-power Frobenius acting on the $\ell$-adic Tate module of an elliptic curve over a finite field. It is used, together with the companion trace computation [`WeierstrassCurve.trace_frobenius_tateModule_eq_card_add_one_sub`](thm.html#WeierstrassCurve.trace_frobenius_tateModule_eq_card_add_one_sub), by the lemmas describing the action of Frobenius on the Tate module in terms of a two-element basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_det_frobenius_tateModule_eq_card.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.det_frobenius_tateModule_eq_card {F : Type*} [Field F] [Fintype F] {k : Type} [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : F) ≠ 0) : LinearMap.det (TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ) = (Fintype.card F : ℤ_[ℓ]) := by sorry
