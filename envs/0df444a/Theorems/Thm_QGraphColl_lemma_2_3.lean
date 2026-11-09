-- Prove2me | Theorems.Thm_QGraphColl_lemma_2_3
-- name    : QGraphColl.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:29.650199+00:00
-- url     : https://prove2.me/theorems/a4eee0dd-1183-400a-9c1f-134f5fcfbc75
-- title:
--   Lemma 2.3 — bipartite reduction: the double cover on $2n$ labels, one original query per copied query
-- statement:
--   Let $G$ be a graph on the vertex set $V$ with $|V|=n$, and let $G_2$ be its bipartite double cover on the $2n$ labels $V\times\{0,1\}$, the label $(v,i)$ carrying the input bit $x_v$. Then
--
--   1. $G_2$ is bipartite with sides $V\times\{0\}$ and $V\times\{1\}$;
--   2. $G_2$ has a marked edge on the copied input exactly when $G$ has one on $x$;
--   3. every copy $(v,i)$ has the degree of $v$ in $G$;
--   4. every $T$-query algorithm with queries to the copied input is simulated by a $T$-query algorithm with queries to $x$, with the same output distribution on every input.
--
--   Hence graph collision on a known graph with $n$ vertices reduces to graph collision on a known bipartite graph with $2n$ labels, with one original query per query to the copied input, preserving the maximum degree.
--
--   Differences from the source:
--   - reading: graph collision on G reduces to graph collision on a bipartite graph with 2n labels, with one original query per query to the copied input → clauses 1, 2 and 4 for the double cover of the proof (v ↦ v₀, v₁; uv ↦ u₀v₁, v₀u₁); reason: the reduction is the construction of the proof, p.13; clause 4 is 'one original query per query' for arbitrary query algorithms
--   - generalization: (not stated in the lemma) → clause 3: deg_{G₂}(v, i) = deg_G(v); reason: used by the proof of Theorem 1.1 ('a bipartite graph on 2n labels whose maximum degree is still at most d', p.31); an extra true conclusion of the same construction
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 2.3 and proof, p.13; the degree clause is used in the proof of Theorem 1.1, p.31

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_restrict

open QAlgorithms

namespace QGraphColl

/-- **Lemma 2.3** (Bipartite reduction; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.13). Graph collision on a known graph with `n`
vertices reduces to graph collision on a known bipartite graph with `2n` labels, with one
original query per query to the copied input.

**Formalization Note.** The bipartite graph is the one of the paper's proof, `doubleCover G` on
`V × Bool` (`2n` labels; vertex `(v, i)` is marked by `x_v`). The four clauses are:
1. it is bipartite with sides `V × {0}` and `V × {1}`;
2. it has a marked edge on the copied input `(v, i) ↦ x_v` exactly when `G` has one on `x`;
3. (used in the proof of Theorem 1.1, p.31: "whose maximum degree is still at most `d`") every
   copy `(v, i)` has the degree of `v`;
4. "one original query per query to the copied input": every `T`-query algorithm with queries to
   the copied input is simulated by a `T`-query algorithm with queries to `x` (workspace
   `Bool × W` holding the copy index), with the same output distribution on every input. -/
theorem lemma_2_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    IsSides (doubleCover G) (Finset.univ.filter fun p => p.2 = false)
      (Finset.univ.filter fun p => p.2 = true) ∧
    (∀ x : V → Bool, gc (doubleCover G) (fun p => x p.1) = gc G x) ∧
    (∀ p : V × Bool, deg (doubleCover G) p = deg G p.1) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (V × Bool) Bool W T)
      (β : Type) [DecidableEq β] (out : ((V × Bool) × Bool) × W → β),
      ∃ (A' : QueryAlg V Bool (Bool × W) T) (out' : (V × Bool) × (Bool × W) → β),
        ∀ (x : V → Bool) (b : β),
          A'.outputProb (xorOracle x) out' b = A.outputProb (xorOracle fun p => x p.1) out b) := by sorry

end QGraphColl
