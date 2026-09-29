-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroup_cycloLift_ne_one
-- name    : ValuationSubring.exists_mem_inertiaSubgroup_cycloLift_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/44b67234-e232-5dd4-b366-f794cad6453e
-- title:
--   Inertia at p moves μₚ for odd p
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which lies over $p$ in the sense of the project predicate `LiesOverPrime`, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$. Let $n$ be an arbitrary function from the group of field automorphisms of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ to $\mathbb{N}$ which pins down the action on $p$-th roots of unity: for every automorphism $\sigma$ and every $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^p = 1$ one has $\sigma\zeta = \zeta^{n(\sigma)}$. The assertion is that there exists an element $\sigma$ of the inertia subgroup `A.inertiaSubgroup ℚ` (a subgroup of the decomposition subgroup of $A$ over $\mathbb{Q}$) whose underlying automorphism satisfies $n(\sigma) \neq 1$ in $\mathbb{Z}/p$. Note that $n$ is only required to satisfy the displayed congruence condition; no multiplicativity or continuity is assumed, and the conclusion is the single inequality $n(\sigma) \not\equiv 1 \pmod p$.
--
--   This is the statement that the mod $p$ cyclotomic character is ramified at $p$ for odd $p$: inertia at a place above $p$ acts non-trivially on $\mu_p$, equivalently $\mathbb{Q}(\mu_p)/\mathbb{Q}$ is ramified at $p$. It is used in the analysis of the $p$-torsion of the Frey curve at the prime $p$, being cited by [`ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt`](thm.html#ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt) and [`ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt_of_five_le`](thm.html#ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroup_cycloLift_ne_one.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_mem_inertiaSubgroup_cycloLift_ne_one (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : AlgebraicClosure ℚ), ζ ^ p = 1 → σ ζ = ζ ^ (n σ)) :
    ∃ σ ∈ A.inertiaSubgroup ℚ, (n (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ZMod p) ≠ 1 := by sorry
