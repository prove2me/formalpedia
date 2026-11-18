-- Prove2me | Theorems.Thm_WeldedPath_verifier_realization
-- name    : WeldedPath.verifier_realization
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T16:28:32.149208+00:00
-- url     : https://prove2.me/theorems/aed21153-968d-40f0-a653-26aa07f66ef9
-- title:
--   Algorithm 3.9 is a query algorithm with at most 7q+3 queries
-- statement:
--   Fix any welded-tree oracle interface with parameters $n,l,G$. Let $A$ make $q\ge1$ queries with finite workspace, and let $o$ map its final measurement outcomes to lists of colored labels. There are a finite workspace, an algorithm $B$ making exactly $7q+3$ queries to the same oracle, and an acceptance event $E$ independent of the sampled permutations, such that for every finite sampling set $S$,
--   $$
--   \mathbb E_{\sigma\in S}\Pr[B^{O_\sigma}\in E]
--   =\mathbb E_{\sigma\in S}\Pr[\operatorname{Accepts}_{3.9}(\sigma,q,o(A^{O_\sigma}))].
--   $$
--   Both expectations use the published finite-average convention, including the empty set. The same $B$ and $E$ work for all $S$.
--
--   This realizes the source's standard-oracle verification procedure in the unitary query-algorithm model, so distribution-comparison lemmas for oracle-independent accepting events apply.
--
--   **Formalization Note.** The exact query count makes the source's $O(q)$ overhead explicit. It includes the original $q$ queries. Graph validity and parity are unnecessary for this operational realization.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/pdf/2611.05912v1, Algorithm 3.9, p.24, steps 2-4; Section 4.5, p.44, the verifier A_ver preceding the probability comparison. The explicit bound 7q+3 and the unitary realization are derived bookkeeping for the stated O(q)-query verification procedure, not a quoted theorem of the source.

import Definitions.Def_WeldedPath_Supplement_pWt

namespace WeldedPath

open QAlgorithms Supplement

/-- Algorithm 3.9 implemented as one query algorithm with a fixed acceptance event.
The bound `7*q+3` is derived by counting its verification queries for `q ≥ 1`:
at most `2*q+4` on the short-output branch and `6*q+3` on the long-output branch,
in addition to the original `q` queries. No validity assumption on `G` is needed
for this operational statement. -/
theorem verifier_realization (n l : ℕ) (G : WeldedInstance n)
    (W : Type) [Fintype W] [DecidableEq W] (q : ℕ) (hq : 1 ≤ q)
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
      List (Fin 3 × Qubits (2 * n + 1))) :
    ∃ (W' : Type) (instF : Fintype W') (instD : DecidableEq W'),
      letI : Fintype W' := instF
      letI : DecidableEq W' := instD
      ∃ (B : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W' (7 * q + 3))
        (acc : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W' → Prop),
        ∀ S : Finset (Equiv.Perm (Label n) × Equiv.Perm G.edges),
          G.probOver l S B (fun _ => acc) =
            G.probOver l S A (fun σ z => Accepts39 l G σ q (out z)) := by sorry

end WeldedPath
