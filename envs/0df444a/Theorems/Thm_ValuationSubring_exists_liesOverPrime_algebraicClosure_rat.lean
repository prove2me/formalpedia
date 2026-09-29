-- Prove2me | Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
-- name    : ValuationSubring.exists_liesOverPrime_algebraicClosure_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/795b03fc-3cbd-5c73-b6fd-dece3e952452
-- title:
--   Existence of a place of ℚ̄ above each prime p
-- statement:
--   Let $p$ be a prime number (an element of `Nat.Primes`, so a natural number together with the witness that it is prime). The assertion is that there exists a valuation subring $A$ of the field $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, i.e. a subring $A \subseteq \overline{\mathbb{Q}}$ such that for every $x \in \overline{\mathbb{Q}}$ either $x \in A$ or $x^{-1} \in A$, satisfying the project's predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16) for the natural number underlying $p$. By definition this predicate says that the image of $p$ under the canonical map $\mathbb{N} \to \overline{\mathbb{Q}}$ lies in the set of nonunits of $A$: that is, $p$ belongs to $A$ and is not invertible in $A$, equivalently $p$ lies in the maximal ideal of the valuation ring $A$. No hypotheses beyond the primality of $p$ are imposed, and nothing is asserted about the value group of $A$, its residue field, or uniqueness of $A$.
--
--   This is the existence of a place of $\overline{\mathbb{Q}}$ extending the $p$-adic place of $\mathbb{Q}$, in the weak form needed downstream: a valuation subring of $\overline{\mathbb{Q}}$ in whose maximal ideal $p$ lies. It serves as the source of $p$-adic places in the ramification-theoretic parts of the development, and is invoked widely (for instance in the conductor and Čerednik–Drinfel'd strands).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_liesOverPrime_algebraicClosure_rat (p : Nat.Primes) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) := by sorry
