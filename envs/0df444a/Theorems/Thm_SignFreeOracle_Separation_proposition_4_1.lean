-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_proposition_4_1
-- name    : SignFreeOracle.Separation.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:03.353779+00:00
-- url     : https://prove2.me/theorems/5e0e982c-f3af-4838-a905-f86910ac763b
-- title:
--   Proposition 4.1 (corrected: integral construction parameters) — full boundary isomorphism
-- statement:
--   For every sufficiently large admissible $n$, every valid base graph and every seed set $U$, write $W$ for the retained vertex set and $\partial U$ for its base-only boundary. The original and truncated graphs obey all three clauses:
--   $$N_F(v)=N_G(v)\ (v\in W\setminus\partial U),\quad N_F(v)=N_G(v)\cap W\subsetneq N_G(v)\ (v\in\partial U),\quad N_F(v)=\varnothing\ (v\notin W).$$
--   For every labelling and every neighbour index, their oracle answers agree off the boundary inside $W$. Moreover $G_n[W]$ is isomorphic to the explicit graph obtained from the induced base graph on $\overline U$ by attaching all its original smaller decorations, and one $\widehat T_{n,K}$ for each base edge leaving the closure. These are disjoint copies. The isomorphism sends the boundary bijectively to exactly their 0-level leaves. This states the full structural and oracle interface used by the exploration bound.
--
--   Differences from the source:
--   - correction: n is an arbitrary positive integer while sqrt(n), depths and bit counts are used as dimensions → all sufficiently large admissible integral n; reason: n=2,k=1 requires 3-sqrt(2) children and is undefined; admissibility includes the unbounded sequence n=4^s
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - generalization: the selected base graph B_n → every base graph satisfying the original connectedness, regularity, size and girth bounds; reason: the proofs use exactly these base properties and specialize to the selected B_n
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
--   - encoding: neighbour positions i in [d] → zero-based natural positions, returning the queried label beyond the neighbour list; reason: positions outside the source query range have a graph-independent self answer and can be simulated without an oracle query
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Proposition 4.1, p. 13 (PDF p. 13)

import Definitions.Def_SignFreeOracle_Separation_Attachment
import Definitions.Def_SignFreeOracle_Separation_Encoding

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

theorem proposition_4_1 : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Admissible n →
    ∀ (NB : ℕ) (B : SimpleGraph (Fin NB)), BaseConditions n NB B →
    ∀ U : Set (Fin (2 ^ bits n)),
      (∀ v ∈ retained n NB B U \ boundary n NB B U,
        (noGraph n NB B U).neighborSet v = (yesGraph n NB B).neighborSet v) ∧
      (∀ v ∈ boundary n NB B U,
        (noGraph n NB B U).neighborSet v = (yesGraph n NB B).neighborSet v ∩ retained n NB B U ∧
        (noGraph n NB B U).neighborSet v ⊂ (yesGraph n NB B).neighborSet v) ∧
      (∀ v ∉ retained n NB B U, (noGraph n NB B U).neighborSet v = ∅) ∧
      (∀ (π : Equiv.Perm (Fin (2 ^ bits n))) x i,
        π.symm x ∈ retained n NB B U \ boundary n NB B U →
        graphQuery (noGraph n NB B U) π x i = graphQuery (yesGraph n NB B) π x i) ∧
      (∃ e : (yesGraph n NB B).induce (retained n NB B U) ≃g
          attachedGraph n NB B (seedClosure n NB B U),
        ∀ v, v.val ∈ boundary n NB B U ↔
          AttachedBoundary n NB B (seedClosure n NB B U) (e v)) := by sorry

end SignFreeOracle.Separation
