-- Prove2me | Theorems.Thm_ValuationSubring_tameCharacter_mul_of_mem_inertiaSubgroupIn
-- name    : ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/b33e7369-0083-5f3a-9b93-d6c016f1a6dd
-- title:
--   Multiplicativity of the tame character on inertia
-- statement:
--   Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ (here $\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`), let $\pi \in \overline{\mathbb{Q}}$ be nonzero, let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ lying in `P.inertiaSubgroupIn ℚ`, that is, in the image under the inclusion of the decomposition subgroup of the inertia subgroup of $P$ over $\mathbb{Q}$, and let $\tau$ be an arbitrary $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$. Writing $\mathrm{tc}_\pi(\rho) :=$ `P.tameCharacter π ρ` for the element of the residue field of the local ring $P$ defined to be the residue class of $\rho(\pi)/\pi$ when this quotient lies in $P$, and $0$ otherwise, the conclusion is the identity $\mathrm{tc}_\pi(\sigma\tau) = \mathrm{tc}_\pi(\sigma)\,\mathrm{tc}_\pi(\tau)$ in that residue field. Thus multiplicativity is asserted with an inertia hypothesis on the left factor only; the right factor $\tau$ is unrestricted, and the cut-off value $0$ on the non-integral branch is part of the assertion.
--
--   This is the homomorphism property of the tame (fundamental) character attached to a place $P$ of $\overline{\mathbb{Q}}$ and a uniformiser-like element $\pi$, in the asymmetric form needed later: the character is multiplicative as soon as the first argument is inertial. It is used in the analysis of the characteristic polynomial of inertia acting on the mod-$\ell$ representations attached to newforms, in the statements about newforms whose level has factorisation exponent two at an odd prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_tameCharacter_mul_of_mem_inertiaSubgroupIn.lean

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ) (hπ : π ≠ 0)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    P.tameCharacter π (σ * τ) = P.tameCharacter π σ * P.tameCharacter π τ := by sorry
