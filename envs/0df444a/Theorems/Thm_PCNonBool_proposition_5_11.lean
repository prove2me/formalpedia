-- Prove2me | Theorems.Thm_PCNonBool_proposition_5_11
-- name    : PCNonBool.proposition_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:04.486427+00:00
-- url     : https://prove2.me/theorems/f0a05441-8049-4c1c-a67a-5c42640f705d
-- title:
--   Proposition 5.11 (corrected: matching clause needs $c > 0$) — partition of $N(S)$ into private neighbourhoods; a matching on $S$
-- statement:
--   **Proposition 5.11.** Let $G=(U\sqcup V,E)$ be an $(s,\Delta,c)$-boundary expander and let $S=\{v_1,\dots,v_\ell\}\subseteq U$ with $|S|\le s$. Then:
--
--   1. there is a partition $\bigsqcup_k R_k$ of $N(S)$ with $R_k\subseteq N(v_k)$ and $|R_k|\ge c$ for every $k$;
--   2. if $c>0$, there is a matching on $S$: an injective map $f:S\to V$ with $(v,f(v))\in E$ for all $v\in S$.
--
--   The matching is the partial assignment of pigeons to holes that Algorithm 1 uses to restore expansion after each split.
--
--   Differences from the source:
--   - correction: "In particular, there is a matching on S" for every real c → the matching clause when 0 < c; reason: for c = 0, U = {u}, V = ∅ and S = {u} the graph is an (s, Δ, 0)-boundary expander and the partition clause holds with R_u = ∅, but u has no hole to be matched to
--   - encoding: a partition ⨆_i R_i of N(S) with R_i ⊆ N(v_i) and |R_i| ≥ c; a matching on S → R : U → Finset V, pairwise disjoint on S, R v ⊆ N(v), c ≤ |R v|, ⋃_{v∈S} R v = ⋃_{v∈S} N(v); f : U → V injective on S with (v, f v) ∈ E; reason: N(S) = ⋃_{v∈S} N(v) for S ⊆ U; same objects
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Proposition 5.11, p.29 (PDF p.32)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_IsBoundaryExpander

namespace PCNonBool

/-- **Proposition 5.11** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.29 (PDF p.32)), corrected. If `G` is an `(s, Δ, c)`-boundary
expander and `S ⊆ U` has size at most `s`, then `N(S)` is partitioned by sets `R_v ⊆ N(v)`,
`v ∈ S`, with `|R_v| ≥ c`; and if `c > 0` there is a matching on `S`.

**Formalization Note** The matching clause as printed fails at `c = 0` (`U = {u}`, `V = ∅`,
`S = {u}`). -/
theorem proposition_5_11 {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (s Δ : ℕ) (c : ℝ) (hG : IsBoundaryExpander G s Δ c)
    (S : Finset U) (hS : S.card ≤ s) :
    (∃ R : U → Finset V, (∀ v ∈ S, R v ⊆ nbrOn G Finset.univ v ∧ c ≤ ((R v).card : ℝ)) ∧
      (S : Set U).PairwiseDisjoint R ∧ S.biUnion R = S.biUnion (nbrOn G Finset.univ)) ∧
    (0 < c → ∃ f : U → V, Set.InjOn f S ∧ ∀ v ∈ S, G.Adj v (f v)) := by sorry

end PCNonBool
