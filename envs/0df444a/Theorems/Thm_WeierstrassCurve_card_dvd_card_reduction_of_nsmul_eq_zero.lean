-- Prove2me | Theorems.Thm_WeierstrassCurve_card_dvd_card_reduction_of_nsmul_eq_zero
-- name    : WeierstrassCurve.card_dvd_card_reduction_of_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/82fe1a47-f0dd-5f80-8ca3-38d0222755ec
-- title:
--   Reduction bounds prime-to-p torsion of E(ℚ)
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $p$ be a prime number such that the image of $p$ in $\mathbb{Z}$ does not divide the discriminant $W.\Delta$, and let $V$ be an affine Weierstrass curve over $\mathbb{Q}$ which is the base change of $W$ along the ring homomorphism $\mathbb{Z}\to\mathbb{Q}$, i.e. $W.\mathrm{map}(\mathbb{Z}\to\mathbb{Q})=V$. Let $n$ be a natural number not divisible by $p$, and let $H$ be an additive subgroup of the group $V.\mathrm{Point}$ of rational points of $V$ (the points of the affine Weierstrass model, with the point at infinity) such that $n\cdot P=0$ for every $P\in H$. Then the cardinality of $H$ divides the cardinality of the group of points of the affine Weierstrass curve over $\mathbb{Z}/p\mathbb{Z}$ obtained from $W$ by base change along $\mathbb{Z}\to\mathbb{Z}/p\mathbb{Z}$. Both cardinalities are taken in the sense of `Nat.card`, so they are $0$ for infinite groups.
--
--   This is the counting form of the classical fact that reduction at a prime of good reduction is injective on torsion of order prime to the residue characteristic; it is the standard device for bounding the rational torsion subgroup of an elliptic curve over $\mathbb{Q}$ by point counts modulo small good primes. It is applied in the analysis of rational points on the modular curve of level $15$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_card_dvd_card_reduction_of_nsmul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.card_dvd_card_reduction_of_nsmul_eq_zero (W : WeierstrassCurve ℤ) {p : ℕ} (hp : p.Prime) (hΔ : ¬ (p : ℤ) ∣ W.Δ) {V : WeierstrassCurve.Affine ℚ} (hV : W.map (Int.castRingHom ℚ) = V) {n : ℕ} (hn : ¬ p ∣ n) (H : AddSubgroup V.Point) (hH : ∀ P ∈ H, n • P = 0) : Nat.card H ∣ Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by sorry
