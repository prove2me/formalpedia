-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_mem_bestResponse_iff
-- name    : SocialEquilibrium.Existence.mem_bestResponse_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:44:09.824906+00:00
-- url     : https://prove2.me/theorems/a182e55b-bf53-456a-a75e-239714a367f3
-- title:
--   Proof of the THEOREM — fixed points of φ are exactly the equilibrium points
-- statement:
--   In Debreu's abstract economy, a profile $a^*$ is a fixed point of the best-response map, $a^*\in\phi(a^*)$, that is,
--   $$a^*_\iota\in M_{\bar a^*_\iota}\quad\text{for all }\iota,$$
--   if and only if $a^*$ is an equilibrium point: $a^*_\iota\in A_\iota(\bar a^*_\iota)$ and $f_\iota(a^*)=\max_{a_\iota\in A_\iota(\bar a^*_\iota)}f_\iota(\bar a^*_\iota,a_\iota)$ for every $\iota$.
--
--   This is the last step of the existence proof: the fixed point produced by the LEMMA is an equilibrium point. The statement holds for arbitrary action sets, constraint maps and payoffs; the "if" direction is the converse, included for completeness.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 889, §2 proof of the THEOREM, last paragraph

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889 (proof of the THEOREM, last paragraph): a profile `a*` is a fixed
point of `φ(a) = M_{ā_1} × ⋯ × M_{ā_ν}`, i.e. `a*_ι ∈ M_{ā*_ι}` for all `ι`, exactly when `a*` is
an equilibrium point. -/
theorem mem_bestResponse_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (a : ∀ j, X j) :
    a ∈ bestResponse X A f a ↔ IsEquilibrium X A f a := by sorry

end SocialEquilibrium.Existence
