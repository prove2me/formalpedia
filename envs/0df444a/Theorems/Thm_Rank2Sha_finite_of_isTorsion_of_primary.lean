-- Prove2me | Theorems.Thm_Rank2Sha_finite_of_isTorsion_of_primary
-- name    : Rank2Sha.finite_of_isTorsion_of_primary
-- status  : Proved
-- author  : @barindersbanwait
-- created : 2026-11-25T01:14:14.257234+00:00
-- url     : https://prove2.me/theorems/2bfcfeaa-de03-429c-a7e7-1b51f4ef13b7
-- title:
--   A torsion abelian group with finitely many nonzero primary parts, each finite, is finite
-- statement:
--   Let $G$ be an abelian group in which every element has finite order, and let $S$ be a finite set of natural numbers. Suppose that
--
--   1. for every prime $p \notin S$, the group $G$ has no element of order $p$, that is, $p x = 0$ implies $x = 0$;
--   2. for every prime $p \in S$, the $p$-primary part $G[p^\infty] = \{ x \in G : p^n x = 0 \text{ for some } n \ge 0 \}$ is finite.
--
--   Then $G$ is finite:
--
--   $$
--   \# G < \infty .
--   $$
--
--   A torsion abelian group is the direct sum of its primary parts, so the hypotheses leave finitely many summands, each finite. The lemma is applied to the Shafarevich–Tate group.
--
--   **Formalization Note** Members of $S$ that are not prime are ignored by both hypotheses.
-- source:
--   Elementary; primary decomposition of a torsion abelian group. Stated for the reduction of the goal of this mission.

import Mathlib

namespace Rank2Sha
theorem finite_of_isTorsion_of_primary {G : Type*} [AddCommGroup G]
    (hT : IsAddTorsion G) (S : Finset ℕ)
    (hout : ∀ p : ℕ, p.Prime → p ∉ S → ∀ x : G, p • x = 0 → x = 0)
    (hin : ∀ p ∈ S, p.Prime → {x : G | ∃ n : ℕ, p ^ n • x = 0}.Finite) :
    Finite G := by sorry
end Rank2Sha
