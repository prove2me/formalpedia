-- Prove2me | Theorems.Thm_WeierstrassCurve_prime_dvd_card_point_of_cofixed_addSubgroup_of_goodReduction
-- name    : WeierstrassCurve.prime_dvd_card_point_of_cofixed_addSubgroup_of_goodReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/cbd51eb6-2046-58df-a7d3-df6dc2b2bf49
-- title:
--   Cofixed p-torsion forces p ∣ #W(𝔽_ℓ)
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $p$ be a natural number assumed prime (through a `Fact` instance). Base change $W$ along $\mathbb{Z}\to\mathbb{Q}$ and view it over the algebraic closure $\bar{\mathbb Q}$, obtaining the group of affine points of $(W.\mathrm{map}\ \mathbb{Z}\to\mathbb{Q})$ over $\bar{\mathbb Q}$, on which an $\mathbb{Q}$-algebra automorphism $\sigma$ of $\bar{\mathbb Q}$ acts by the project's action $\sigma\bullet P=\mathrm{Point.map}\ \sigma\ P$. Let $N$ be an arbitrary additive subgroup of that point group (no Galois stability, no $\mathbb{Z}/p$-module structure and no one-dimensionality is assumed). Let $\ell$ be a prime with $\ell\nmid p$ and $\ell\nmid\Delta_W$ (good reduction of the given model at $\ell$ in the sense that the discriminant `W.Δ` is not divisible by $\ell$). Let $A$ be a valuation subring of $\bar{\mathbb Q}$ lying over $\ell$ in the project's sense `LiesOverPrime`, i.e. the image of $\ell$ lies in the non-units of $A$, and let $\sigma$ be a Frobenius element at $A$ in the project's sense `IsFrobeniusAt`: $\sigma$ belongs to the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x\mapsto x^{\ell}$. Assume the cofixing hypothesis: for every point $y$ with $p\cdot y=0$ one has $\sigma\bullet y-y\in N$. Assume finally that some point $e$ satisfies $p\cdot e=0$ and $e\notin N$. The conclusion is that $p$ divides the number of points of the base change of $W$ to $\mathbb{Z}/\ell$, that is, $p\mid \#W(\mathbb{F}_\ell)$, where the number of points is taken in the naturals and is $0$ should that group be infinite.
--
--   This is the finite-level form of the point-counting step used in Mazur's analysis of $p$-torsion with a $\sigma$-cofixed quotient (B. Mazur, Modular curves and the Eisenstein ideal, 1977): if Frobenius at $\ell$ acts trivially on $W[p]/N$ while $W[p]\not\subseteq N$, then the Frobenius characteristic polynomial forces $p\mid\#W(\mathbb{F}_\ell)$. The formal statement is deliberately weaker in its hypotheses than the textbook version: $N$ is merely an additive subgroup of the full group of $\bar{\mathbb Q}$-points, the cofixing condition is imposed only for the single automorphism $\sigma$ and only on $p$-torsion, and good reduction is taken to mean non-divisibility of the discriminant of the chosen model. It is used in the Frey-curve argument [`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large), where it rules out a Galois-stable cofixed line for $p\ge 17$ by comparing the resulting divisibility with crude bounds on point counts at a small prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_prime_dvd_card_point_of_cofixed_addSubgroup_of_goodReduction.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

theorem WeierstrassCurve.prime_dvd_card_point_of_cofixed_addSubgroup_of_goodReduction
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (N : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ¬ ℓ ∣ p) (hgood : ¬ (ℓ : ℤ) ∣ W.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (hcof : ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p • y = 0 → σ • y - y ∈ N)
    (e : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (he : p • e = 0) (heN : e ∉ N) :
    p ∣ Nat.card (W⁄(ZMod ℓ)).Point := by sorry
