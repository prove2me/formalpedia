-- Prove2me | Theorems.Thm_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime
-- name    : ValuationSubring.algebraMap_rat_mem_iff_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/5db011d4-c095-5f15-b61b-de74db45e666
-- title:
--   A place of ℚ̄ above q meets ℚ in mathbb Z_{(q)}
-- statement:
--   Let $A$ be a valuation subring of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$, let $q$ be a natural number that is prime, and assume `A.LiesOverPrime q`, that is, the image of $q$ in $\overline{\mathbb Q}$ lies in the set of nonunits of $A$ (equivalently, $A$-valuation of $q$ is $<1$, so $q$ belongs to the maximal ideal of $A$). Then for every rational number $x$, the image of $x$ under the structure map $\mathbb Q \to \overline{\mathbb Q}$ belongs to $A$ if and only if $x$ belongs to the valuation subring of the $q$-adic valuation `Rat.padicValuation q` on $\mathbb Q$, i.e. if and only if $v_q(x) \ge 0$. Thus the contraction of $A$ to $\mathbb Q$ is exactly the localisation $\mathbb Z_{(q)}$, stated as a membership equivalence rather than as an equality of subrings.
--
--   This identifies the place of $\mathbb Q$ induced by a place of $\overline{\mathbb Q}$ lying above the rational prime $q$: valuation rings of $\mathbb Q$ in which $q$ is a nonunit are the $q$-adic ones. It serves as a bridge lemma wherever rational coordinates must be tested for integrality at a chosen place of $\overline{\mathbb Q}$, and is used in the study of reduction of Weierstrass curves and of inertia at $q$ acting on finite flat group schemes, as well as in constructing the ring homomorphism attached to $A$ on the localisation of $\mathbb Z$ at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.algebraMap_rat_mem_iff_of_liesOverPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime] (hA : A.LiesOverPrime q) (x : ℚ) :
    algebraMap ℚ (AlgebraicClosure ℚ) x ∈ A ↔ x ∈ (Rat.padicValuation q).valuationSubring := by sorry
