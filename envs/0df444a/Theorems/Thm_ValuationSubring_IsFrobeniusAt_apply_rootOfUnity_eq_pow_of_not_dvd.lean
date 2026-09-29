-- Prove2me | Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow_of_not_dvd
-- name    : ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/cfb33b6c-fc11-592e-8249-051af2c91143
-- title:
--   Frobenius acts as q-th power on roots of unity of order prime to q
-- statement:
--   Let $q$ be a prime number and let $A$ be a valuation subring of an algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ which lies over $q$, in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ belongs to the set of nonunits of $A$. Let $\sigma$ be an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ which is a Frobenius element at $A$ for $q$: that is, $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ (so $\sigma$ preserves $A$ and hence acts on the residue field of $A$), and the induced action of $\sigma$ on the residue field $A/\mathfrak{m}_A$ is $x \mapsto x^{q}$ for every residue class $x$. Let $m$ be a natural number with $q \nmid m$, and let $\zeta \in \overline{\mathbb{Q}}$ satisfy $\zeta^{m} = 1$. Then $\sigma(\zeta) = \zeta^{q}$. Thus the congruence $\sigma(\zeta) \equiv \zeta^{q}$ modulo the maximal ideal of $A$, which holds by definition, is in fact an equality in $\overline{\mathbb{Q}}$ for roots of unity of order prime to $q$.
--
--   This is the standard computation of the action of a Frobenius element on the $m$-th roots of unity for $q \nmid m$, i.e. the statement that the cyclotomic character is unramified at $q$ and sends a Frobenius at $q$ to $q$. It is used in the project when Frobenius traces of elliptic curves and of Galois representations attached to modular curves are computed at a place over $q$, for instance in identifying Frobenius actions on Tate modules and in the analysis of the reduction of mod-$\ell$ representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow_of_not_dvd.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

theorem ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow_of_not_dvd
    {q : ℕ} (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ q)
    {m : ℕ} (hm : ¬ q ∣ m) (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ q := by sorry
