-- Prove2me | Theorems.Thm_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt
-- name    : WeierstrassCurve.mazurStepThree_not_inZeroComponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/1a5d623c-f8e4-5f4c-bac3-03bb04f205b3
-- title:
--   Mazur's Step 3 at one multiplicative prime ℓ
-- statement:
--   Let $p$ be a prime not lying in $\{2,3,5,7,13\}$, let $W$ be a Weierstrass curve over $\mathbb Z$ with $\Delta(W)\neq 0$, and let $Q$ be a point of the affine curve obtained from $W$ by base change along $\mathbb Z\to\mathbb Q$ and then to $\overline{\mathbb Q}=\mathrm{AlgebraicClosure}\ \mathbb Q$, subject to: $\sigma\bullet Q=Q$ for every $\mathbb Q$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}$, and $\mathrm{addOrderOf}\ Q=p$. Assume the multiplicative-type conditions $2\mid\Delta(W)$, $2\nmid c_4(W)$ and $3\mid\Delta(W)$, $3\nmid c_4(W)$, together with the two anchor hypotheses: for every valuation subring $A$ of $\overline{\mathbb Q}$ with $2$ (respectively $3$) a non-unit of $A$ — this is the project's [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), i.e. $(q:\overline{\mathbb Q})\in A.\mathrm{nonunits}$ — one has $\neg\,W.\mathrm{InZeroComponentAt}\ A\ Q$. Let finally $\ell$ be a prime with $\ell\neq p$, $\ell\mid\Delta(W)$, $\ell\nmid c_4(W)$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $\ell$ is a non-unit. The conclusion is $\neg\,W.\mathrm{InZeroComponentAt}\ A\ Q$. Here the project's predicate $W.\mathrm{InZeroComponentAt}\ A\ P$ says: either $P=0$, or $P=(x,y)$ for a nonsingular affine point with coordinates in $\overline{\mathbb Q}$ such that either $x\notin A$, or both $x,y\in A$ and the images of $x,y$ in the residue field of $A$ form a nonsingular point of $W$ base-changed to that residue field. So the assumptions and the conclusion assert that $Q$ is a nonzero affine point with $x\in A$ for which no such nonsingular reduction exists (at the relevant $A$). No minimality or semistability of the model is assumed, and nothing is asserted at $\ell=p$.
--
--   This is Mazur's "Step 3" from the proof of Theorem 8 in chapter III, §5 of Modular curves and the Eisenstein ideal: a rational point of prime order $p\notin\{2,3,5,7,13\}$ that lies off the identity component at the primes $2$ and $3$ lies off it at every other prime of multiplicative reduction. Relative to the textbook statement the Lean version is per-prime and purely local in its data: the hypotheses at $2$, $3$ and $\ell$ concern only divisibility of $\Delta$ and $c_4$ by those primes, the "places" are arbitrary valuation subrings of $\overline{\mathbb Q}$ in which the prime in question is a non-unit, and the case $\ell=p$ is excluded. It is the single global input to [`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large), the $p\ge 17$ case of the exclusion of a Galois-stable line with trivial quotient action for the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt.lean

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.mazurStepThree_not_inZeroComponentAt
    {p : ℕ} (hp : p.Prime) (hp' : p ∉ ({2, 3, 5, 7, 13} : Finset ℕ))
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q)
    (hQord : addOrderOf Q = p)
    (h2Δ : (2 : ℤ) ∣ W.Δ) (h2c₄ : ¬ (2 : ℤ) ∣ W.c₄)
    (h2 : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 → ¬ W.InZeroComponentAt A Q)
    (h3Δ : (3 : ℤ) ∣ W.Δ) (h3c₄ : ¬ (3 : ℤ) ∣ W.c₄)
    (h3 : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 → ¬ W.InZeroComponentAt A Q)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hℓΔ : (ℓ : ℤ) ∣ W.Δ) (hℓc₄ : ¬ (ℓ : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    ¬ W.InZeroComponentAt A Q := by sorry
