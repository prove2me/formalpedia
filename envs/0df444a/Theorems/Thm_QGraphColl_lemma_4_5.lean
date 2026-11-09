-- Prove2me | Theorems.Thm_QGraphColl_lemma_4_5
-- name    : QGraphColl.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:35.152238+00:00
-- url     : https://prove2.me/theorems/1cb23982-f375-4aa4-8f3b-61a237b7bf66
-- title:
--   Lemma 4.5 — extraction and coefficient bounds (4.2) with $\tilde O(\sqrt m[s_A^{-1/3}(\theta_B/\theta_A)^{1/6}+s_A^{-1/2}+\sqrt{d_A/\delta}])$ queries
-- statement:
--   Let $n=|V|\ge2$ and let $G$ satisfy the input conditions of Algorithm 7: $G$ is bipartite with sides $A,B$, $\deg(v)\le d_A$ for $v\in A$ and $\deg(w)\le d_B$ for $w\in B$, and (a condition on the input $x$) every $v\in A$ has at most $\theta_B$ and every $w\in B$ at most $\theta_A$ marked neighbours; let $\theta_A,\theta_B>0$, $s_A\ge1$, $\delta>0$ and $m=|E(G)|$. For every $c>0$ there are $C,K$ (independent of all of these) such that the following holds.
--
--   The algorithm records, using the graph only, at most one graph $H_u$ per row $u\in A$ (pairwise edge-disjoint subgraphs of $G$), deletes them, and outputs $G'=G\setminus\bigcup_uH_u$. It tests the recorded graphs with
--   $$\tilde O\Big(\sqrt m\big[s_A^{-1/3}(\theta_B/\theta_A)^{1/6}+s_A^{-1/2}+\sqrt{d_A/\delta}\big]\Big)\qquad(4.1)$$
--   queries, accepting every input with a marked edge in some $H_u$ and rejecting every negative input satisfying the input conditions, with error at most $n^{-c}$. On a negative input satisfying the input conditions, every row $u\in A$ has a set $E_u\subseteq A$ such that
--   $$\sum_{v\in M\cap E_u}c_{uv}\le\delta,\qquad\sum_{v\in M\cap(A\setminus E_u)}c_{uv}^2\le2s_A\theta_Ad_A=:v_A,\qquad(4.2)$$
--   where $c_{uv}$ is the common-neighbour count in the output graph, and the same sets keep (4.2) in every graph obtained from the output by further edge deletions. Every collision of $G$ lies in a recorded graph or survives in the output.
--
--   Running the routine with $A$ and $B$ exchanged gives the bounds for rows in $B$ with $v_B=2s_B\theta_Bd_B$.
--
--   Differences from the source:
--   - encoding: Õ(B) and 'the assigned error probability' → ∃ C, K (chosen after the error exponent c, before the vertex type and all parameters) with T ≤ C·B·(log₂ n)^K, n = |V| ≥ 2, and error ≤ n^{−c} for every c > 0; reason: the paper's conventions: Õ suppresses factors polynomial in log n and logarithms are base two (p.12); error probabilities are inverse polynomial in n (p.14)
--   - reading: the named procedure Algorithm 7 (prepare_estimates): its extraction (recorded graphs H_u, output G \ ⨆ H_u) and its test (line 8) has the stated cost and guarantees → there is a T-query algorithm (QueryAlg, workspace Fin m) with that cost and those guarantees; reason: the procedure is a schema over black-box subroutines, so it is not one fixed object; the existence of a procedure with the printed cost and guarantees is what later proofs use (paper.md decision 4)
--   - encoding: θ_A, θ_B in (4.1) and the input conditions → θ_A > 0 and θ_B > 0; reason: θ_B/θ_A is undefined at θ_A = 0; Algorithm 9 supplies θ_A, θ_B > 0
--   - reading: (4.2) in the output graph; subsequent edge deletions preserve these coefficient bounds → one E_u for which (4.2) holds with c = cn G'' for every G'' ≤ G \ ⨆ H_u; reason: the output graph is the case G'' = G \ ⨆ H_u; the proof keeps 'the same exceptional sets' (p.27)
--   - reading: running the routine with A and B exchanged gives the corresponding bounds for rows in B → no separate clause: the lemma applied to (G, B, A); reason: the statement is symmetric in the roles of the sides
--   - generalization: G bipartite with vertex sets A and B (V(G) = A ∪ B) → IsSides G A B on a vertex type that may contain further labels outside A ∪ B; reason: labels outside A ∪ B are isolated; taking V = A ∪ B gives the source's statement
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 4.5 and (4.1), (4.2), pp.25–26 (Algorithm 7 prepare_estimates and its input conditions, p.25)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol
import Definitions.Def_QGraphColl_restrict
import Definitions.Def_QGraphColl_eventProb

open QAlgorithms

namespace QGraphColl

/-- **Lemma 4.5** (Extraction and coefficient bounds; A. Cornelissen, A. S. Gilani, S. Kintali,
F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum barriers for Graph Collision*,
arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), pp.25–26). Let `G` satisfy the input
conditions of Algorithm 7, and let `m = |E(G)|`. For any `s_A ≥ 1` and `δ > 0`, the algorithm records
at most one graph per row `u ∈ A` and uses
`Õ(√m [s_A^{-1/3} (θ_B/θ_A)^{1/6} + s_A^{-1/2} + √(d_A/δ)])` (4.1) queries. On a negative input,
every row `u ∈ A` of the output graph has a set `E_u ⊆ A` such that
`∑_{v ∈ M ∩ E_u} c_uv ≤ δ` and `∑_{v ∈ M ∩ (A \ E_u)} c_uv² ≤ 2 s_A θ_A d_A =: v_A` (4.2).
Here `c_uv` denotes the common neighbor count in the output graph. On a positive input, a collision
is detected or survives, except with the assigned error. Running the routine with `A` and `B`
exchanged gives the corresponding bounds for rows in `B`, with `v_B = 2 s_B θ_B d_B`; subsequent
edge deletions preserve these coefficient bounds.

**Formalization Note.**
* Input conditions of Algorithm 7 (p.25): `G` bipartite with sides `A, B`; `deg(v) ≤ d_A` on `A`,
  `deg(w) ≤ d_B` on `B`; every `v ∈ A` has at most `θ_B` marked neighbours and every `w ∈ B` at most
  `θ_A` (the last two depend on the input `x`, written `Cond x` below); `s_A ≥ 1`, `δ > 0`.
  `θ_A, θ_B > 0` because `θ_B/θ_A` occurs in (4.1) (Algorithm 9 supplies them positive).
* Algorithm 7 is stated as the existence of what it produces. Its extraction uses only the known
  graph: the recorded graph of row `u` is `H u` (`⊥` for `u ∉ A`, at most one per row), the `H u`
  are pairwise edge-disjoint subgraphs of `G`, and the output graph is `G \ ⨆ u, H u`. Its quantum
  part (line 8) is a `T`-query test with `T ≤ C · (4.1) · (log₂ n)^K` that decides whether some
  recorded graph has a marked edge, with error `≤ n^{-c}` on every input positive for a recorded
  graph and on every negative input satisfying the input conditions.
* (4.2) is stated for every graph `G'' ≤` the output graph (`G''` = the output itself, and
  "subsequent edge deletions preserve these coefficient bounds"), with the same `E_u`; `c_uv` is the
  common-neighbour count in `G''`.
* A collision of `G` lies in a recorded graph or survives in the output graph.
* The `B`-side statement is this lemma applied with the sides exchanged.
* `Õ` hides `(log₂ n)^K`, `n = |V| ≥ 2`, `C, K` chosen after the error exponent `c` and before the
  vertex type and all parameters. -/
theorem lemma_4_5 :
    ∀ c : ℝ, 0 < c → ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (A B : Finset V), IsSides G A B →
      ∀ (dA dB : ℝ), (∀ v ∈ A, (deg G v : ℝ) ≤ dA) → (∀ w ∈ B, (deg G w : ℝ) ≤ dB) →
      ∀ (θA θB sA δ : ℝ), 0 < θA → 0 < θB → 1 ≤ sA → 0 < δ →
        let Cond : (V → Bool) → Prop := fun x =>
          (∀ v ∈ A, ((nbr G v ∩ marked x).card : ℝ) ≤ θB) ∧
          (∀ w ∈ B, ((nbr G w ∩ marked x).card : ℝ) ≤ θA)
        ∃ H : V → SimpleGraph V,
          (∀ u, u ∉ A → H u = ⊥) ∧ (∀ u, H u ≤ G) ∧
          Pairwise (fun u u' => Disjoint (H u) (H u')) ∧
          (∃ T : ℕ, (T : ℝ) ≤ C * (Real.sqrt (numEdges G : ℝ) *
                (sA ^ (-(1 : ℝ) / 3) * (θB / θA) ^ ((1 : ℝ) / 6) + sA ^ (-(1 : ℝ) / 2) +
                  Real.sqrt (dA / δ))) * Real.logb 2 (Fintype.card V : ℝ) ^ K ∧
            ∃ (m : ℕ) (Alg : QueryAlg V Bool (Fin m) T) (out : (V × Bool) × Fin m → Bool),
              Alg.ComputesWithError out
                (dom fun x => (∃ u, gc (H u) x = true) ∨ (gc G x = false ∧ Cond x))
                (fun x => decide (∃ u, gc (H u) x = true)) ((Fintype.card V : ℝ) ^ (-c))) ∧
          (∀ x : V → Bool, gc G x = false → Cond x → ∀ u ∈ A, ∃ E ⊆ A,
            ∀ G'' : SimpleGraph V, G'' ≤ G \ (⨆ u', H u') →
              (∑ v ∈ marked x ∩ E, (cn G'' u v : ℝ)) ≤ δ ∧
              (∑ v ∈ marked x ∩ (A \ E), (cn G'' u v : ℝ) ^ 2) ≤ 2 * sA * θA * dA) ∧
          (∀ x : V → Bool, gc G x = true →
            gc (G \ (⨆ u, H u)) x = true ∨ ∃ u, gc (H u) x = true) := by sorry

end QGraphColl
