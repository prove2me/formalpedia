-- Prove2me | Theorems.Thm_RobersonCx_lemma_14
-- name    : RobersonCx.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:58.271368+00:00
-- url     : https://prove2.me/theorems/f4d5faf2-55a0-48e5-81fa-fc22fdd9683f
-- title:
--   Lemma 14 — a balanced separator from a tree decomposition of width $\le k$
-- statement:
--   Let $G$ be a graph on $n\ge1$ vertices and $k\ge0$ an integer with $\mathrm{tw}(G)\le k$. Then there is a set $W\subseteq V(G)$ with $|W|\le k+1$ such that every connected component $C$ of $G-W$ satisfies
--   $$|C|\le n/2\qquad\text{and}\qquad|N_G(C)|\le k,$$
--   where $N_G(C)=\{v\notin C : uv\in E(G)\text{ for some }u\in C\}$ is the external neighbourhood.
--
--   This separator lemma is the tool for the treewidth lower bound of Lemma 15.
--
--   Differences from the source:
--   - encoding: $|C|\le n/2$ → $2|C|\le n$ in $\mathbb N$; reason: avoids division; same instances
--   - encoding: component $C$ of $G-W$ → connected component of the subgraph induced on $V\setminus W$, identified with its vertex set in $V$; reason: the paper identifies a subgraph with its vertex set (p.5)
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Lemma 14, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_RobersonCx_TwLE

set_option autoImplicit false

namespace RobersonCx

/-- Lemma 14 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. A.4, p.14 (PDF p.16)). Let `G` be a nonempty graph on `n` vertices, and let `k` be a
nonnegative integer with `tw(G) ≤ k`. There is a set `W ⊆ V(G)` with `|W| ≤ k + 1` such that every component
`C` of `G − W` satisfies `|C| ≤ n/2` and `|N_G(C)| ≤ k`.

**Formalization Note** `n = Nat.card V` and `|C| ≤ n/2` is `2|C| ≤ n`. A component of `G − W` is a connected
component of the induced subgraph on `V ∖ W`, identified with its vertex set in `V`; `N_G(C)` is the external
neighbourhood `{v ∉ C : uv ∈ E(G) for some u ∈ C}` (p.5). "Nonempty graph" is a nonempty vertex set. -/
theorem lemma_14 {V : Type} [Finite V] [Nonempty V] (G : SimpleGraph V) (k : ℕ) (hk : TwLE G k) :
    ∃ W : Set V, W.ncard ≤ k + 1 ∧ ∀ C : (G.induce Wᶜ).ConnectedComponent,
      2 * (Subtype.val '' C.supp).ncard ≤ Nat.card V ∧
      {v : V | v ∉ Subtype.val '' C.supp ∧ ∃ u ∈ Subtype.val '' C.supp, G.Adj u v}.ncard ≤ k := by sorry

end RobersonCx
