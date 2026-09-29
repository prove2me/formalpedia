-- Prove2me | Theorems.Thm_ValuationSubring_residue_eq_one_of_pow_prime_pow_eq_one
-- name    : ValuationSubring.residue_eq_one_of_pow_prime_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/70a1a6b5-0d99-5e00-ba5b-2bb6db2e69e7
-- title:
--   Residue 1 for p-power roots of unity above p
-- statement:
--   Let $P$ be a valuation subring of the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$, let $p$ be a prime number, and assume `P.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ lies in the set of nonunits of $P$ (the maximal ideal of the local ring $P$). Let $\zeta \in \overline{\mathbb{Q}}$ satisfy $\zeta^{p^n} = 1$ for some natural number $n$, and assume $\zeta \in P$. Then the image of the element $\zeta$ of $P$ under the residue map `IsLocalRing.residue P` from $P$ to its residue field equals $1$. Note that $n$ is arbitrary, with no condition relating it to $\zeta$ beyond $\zeta^{p^n}=1$; in particular the case $n = 0$ forces $\zeta = 1$ and is included.
--
--   This is the elementary statement that the reduction of a $p$-power root of unity at a place above $p$ is trivial, the residue field there being of characteristic $p$. It separates the $p$-power part from the tame part in the computations of characters attached to inertia, and is used in the analysis of the tame character on roots of unity, in the inertia-eigenvector statement for $p$-adic Galois representations attached to cusp forms, and in the semistable covering computations on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_residue_eq_one_of_pow_prime_pow_eq_one.lean

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.residue_eq_one_of_pow_prime_pow_eq_one
    (P : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime) (hP : P.LiesOverPrime p)
    {ζ : AlgebraicClosure ℚ} {n : ℕ} (hζ : ζ ^ p ^ n = 1) (hζP : ζ ∈ P) :
    IsLocalRing.residue P ⟨ζ, hζP⟩ = 1 := by sorry
