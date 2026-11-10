-- Prove2me | Theorems.Thm_RevRedSAT_proposition_5_1
-- name    : RevRedSAT.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:00.15673+00:00
-- url     : https://prove2.me/theorems/50ed6554-1c49-423f-b8a5-4434afebfda3
-- title:
--   Proposition 5.1 — the Nemhauser–Trotter kernel with reconstruction
-- statement:
--   There is a polynomial-time algorithm that, given a Vertex Cover instance $(G,k)$, either correctly reports that $G$ has no vertex cover of size at most $k$, or outputs a vertex set $V'$ (the induced subgraph $G'=G[V']$), an integer $0\le k'\le k$ and a set $P\subseteq V(G)\setminus V'$ such that
--
--   1. $|V'|\le 2k'$ and $|P|=k-k'$;
--   2. $G$ has a vertex cover of size at most $k$ if and only if $G'$ has one of size at most $k'$;
--   3. every vertex cover $Y$ of $G'$ with $|Y|\le k'$ lifts to the vertex cover $P\cup Y$ of $G$.
--
--   The proposition is the classical kernel of Nemhauser and Trotter, cited by the paper with its reconstruction guarantee; it reduces Vertex Cover to an instance on at most $2k$ vertices.
--
--   **Formalization Note** The induced subgraph is output as its vertex set; a vertex cover of $G[V']$ is a set $Y\subseteq V'$ meeting every edge of $G$ inside $V'$.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: in polynomial time → a finite-alphabet machine and constants C, e chosen before the input, time ≤ C·(input size + 1)^e; reason: the standard meaning, with the constants fixed before the input
--   - encoding: an induced subgraph G′ → its vertex set V′ ⊆ V(G); covers of G′ are sets Y ⊆ V′ meeting the edges of G inside V′; reason: an induced subgraph is determined by its vertex set
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Proposition 5.1, p.35 (printed) = PDF p.37

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_VCInstance

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- **Proposition 5.1 (Nemhauser–Trotter kernel with reconstruction).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Proposition 5.1, p.35: "There is a polynomial-time algorithm that, given (G, k), either
correctly determines that G has no vertex cover of size at most k, or produces an induced subgraph
G′, an integer 0 ≤ k′ ≤ k, and a set P ⊆ V(G) \ V(G′) such that 1. |V(G′)| ≤ 2k′ and |P| = k − k′;
2. G has a vertex cover of size at most k if and only if G′ has one of size at most k′; 3. every
vertex cover Y of G′ of size at most k′ lifts to the vertex cover P ∪ Y of G."

There are a finite-alphabet machine and constants `C, e` such that on every code `w` of every
Vertex Cover instance `(G, k)`, within `C·(|w| + 1)^e` steps, the machine outputs either `[false]`,
and then `G` has no vertex cover of size at most `k`; or `true` followed by a listing of a vertex set
`V'` (the induced subgraph `G' = G[V']`), the number `k'`, and a listing of a set `P`, such that
`k' ≤ k`, `P ∩ V' = ∅`, `|V'| ≤ 2k'`, `|P| = k − k'`, `G` has a vertex cover of size at most `k` iff
`G[V']` has one of size at most `k'`, and every vertex cover `Y ⊆ V'` of `G[V']` with `|Y| ≤ k'`
gives the vertex cover `P ∪ Y` of `G`.

**Formalization Note** The induced subgraph is represented by its vertex set `V' ⊆ V(G)`; a vertex
cover of `G[V']` is a set `Y ⊆ V'` meeting every edge of `G` inside `V'` (`CoversInduced`). The
paper cites this result (Nemhauser–Trotter) without proof. -/
theorem proposition_5_1 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C e : ℕ,
      ∀ (I : VCInstance) (w : List Bool), IsVCCode I w →
        ∃ out : List Bool, HMBinPacking.OutputsWithin M w out (C * (w.length + 1) ^ e) ∧
          ((out = [false] ∧ ¬ ∃ S, VCValid I S) ∨
            ∃ (V' P : Finset (Fin I.n)) (k' : ℕ) (L₁ L₂ : List (Fin I.n)),
              L₁.Nodup ∧ L₁.toFinset = V' ∧ L₂.Nodup ∧ L₂.toFinset = P ∧
              out = true :: (encSet L₁ ++ encNat k' ++ encSet L₂) ∧
              k' ≤ I.k ∧ Disjoint P V' ∧ V'.card ≤ 2 * k' ∧ P.card = I.k - k' ∧
              ((∃ S, VCValid I S) ↔ ∃ Y ⊆ V', CoversInduced I.G V' Y ∧ Y.card ≤ k') ∧
              ∀ Y ⊆ V', CoversInduced I.G V' Y → Y.card ≤ k' → IsVertexCover I.G (P ∪ Y)) := by sorry

end RevRedSAT
