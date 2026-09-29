-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/11950875-7443-50dd-b989-bc3281ad1700
-- title:
--   Inertia above 2 acts by ζ ↦ ζ³ on μ₄
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb Q}$ (the chosen algebraic closure `AlgebraicClosure ℚ`) satisfying `A.LiesOverPrime 2`, that is, the image of $2$ in $\overline{\mathbb Q}$ lies in the set of nonunits of $A$, so that $A$ is a valuation ring of $\overline{\mathbb Q}$ whose maximal ideal contains $2$. The assertion is that the subgroup `A.inertiaSubgroupIn ℚ` of the group $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ of $\mathbb Q$-algebra automorphisms of $\overline{\mathbb Q}$ — namely the image of the inertia subgroup of $A$ over $\mathbb Q$ under the inclusion of the decomposition subgroup of $A$ over $\mathbb Q$ into the full automorphism group — contains an element $\sigma$ with the property that $\sigma \zeta = \zeta^3$ for every $\zeta \in \overline{\mathbb Q}$ with $\zeta^4 = 1$. Since $\pm 1$ are fixed by every automorphism and $(-i)^3 = i$, the content is the existence of an inertia element at the given place above $2$ sending $i$ to $-i$.
--
--   This records that $\mathbb Q(i)/\mathbb Q$ is ramified at $2$, so that inertia at any place of $\overline{\mathbb Q}$ above $2$ surjects onto $\mathrm{Gal}(\mathbb Q(i)/\mathbb Q)$; the corresponding statement above an odd prime is false. It is used in the analysis of $2$-power torsion in the toric part of the Jacobian of a modular curve, where a Galois-fixed $4$-torsion point $x$ must satisfy $x = 3x$ and hence $2x = 0$, and in the study of inertial behaviour of $\ell$-adic Galois representations with cyclotomic determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one.lean

import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ 4 = 1 → σ ζ = ζ ^ 3 := by sorry
