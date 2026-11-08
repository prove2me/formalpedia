-- Prove2me | Theorems.Thm_PercCubeCycles_proposition_3_1
-- name    : PercCubeCycles.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:48.677103+00:00
-- url     : https://prove2.me/theorems/9405e984-ec35-4d1d-b532-7e01bb94bd83
-- title:
--   Proposition 3.1 — joining marked trees: if $\beta^k<1/r$ then $G$ has a cycle of length at least $\sum_i d(B_i)$, in $O(|E|^2)$ time
-- statement:
--   Let $n,k,r,d,s\ge1$ be integers, $G$ an $n$-vertex graph and $G_0,\dots,G_k$ pairwise vertex-disjoint subgraphs of $G$. For $*\in\{+,-\}$, $i\in[r]$ and $j\in\{0,\dots,k\}$, let $S^*_{i,j}\subseteq V(G_j)$ have size $s$, with all these sets pairwise disjoint. Suppose:
--
--   1. (a) there are pairwise vertex-disjoint trees $T_1,\dots,T_r\subseteq G_0$ such that each $B_i=(T_i,S^+_{i,0},S^-_{i,0})$ is a marked tree;
--   2. (b) $G$ contains a perfect matching $M^*_{i,j}$ between $S^*_{i,j}$ and $S^*_{i,j+1}$ for all $*$, $i$ and $j\in\{0,\dots,k-1\}$;
--   3. (c) for every $j\in[k]$ and $A\subseteq V(G_j)$ with $|A|\le2|V(G_j)|/3$, $|N_{G_j}(A)|\ge|A|/d^2$.
--
--   Let $\beta=100d^4\log n/s$. If $\beta^k<1/r$, then $G$ contains a cycle of length at least $\sum_{i\in[r]}d(B_i)$, and such a cycle can be found in $O(|E(G)|^2)$ time.
--
--   This turns a packing of long paths into one long cycle.
--
--   Differences from the source:
--   - encoding: the integer $\ell\ge1$ in the list of integers → dropped; reason: it is used nowhere in the statement
--   - reading: time bound with no machine named → one program and one constant $K$ for all instances, at most $K|E(G)|^2$ steps on every coin sequence and for every admissible word width; reason: the paper names no machine; this is the published word RAM with every instruction charged one step
--   - encoding: an instance → words listing $n,k,r,d,s$, then $G$, $G_1,\dots,G_k$, the trees, the sets and the matchings $M^*_{i,j}$; reason: the data are given to the algorithm; $G_0$ enters only through the trees, and the edge-list form keeps the input size $O(|E|)$
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Proposition 3.1, p.9

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_PercCubeCycles_Joining

set_option autoImplicit false

open MatroidSensOracle

namespace PercCubeCycles

/-- Proposition 3.1, p.9, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). Let `n, k, r, d, s ≥ 1`, `G` an `n`-vertex graph, `G₀, …, G_k` pairwise
vertex-disjoint subgraphs, and `S^∗_{i,j} ⊆ V(G_j)` pairwise disjoint sets of size `s` such that (a) there
are pairwise vertex-disjoint trees `Tᵢ ⊆ G₀` with `Bᵢ = (Tᵢ, S^+_{i,0}, S^−_{i,0})` marked trees, (b) `G` contains
perfect matchings between `S^∗_{i,j}` and `S^∗_{i,j+1}`, and (c) for `j ∈ [k]` and `A ⊆ V(G_j)` with
`|A| ≤ 2|V(G_j)|/3`, `|N_{G_j}(A)| ≥ |A|/d²`. With `β = 100d⁴ log n / s`, if `β^k < 1/r` then `G` contains a
cycle of length at least `∑_{i ∈ [r]} d(Bᵢ)`, and such a cycle can be found in `O(|E(G)|²)` time.

**Formalization Note.** The time clause is read on the word RAM: one program and one `K` for all
instances, on every coin sequence and every admissible word width. The output is the length of
the cycle and then its vertices. -/
theorem proposition_3_1 :
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k r d s : ℕ) (D : JoinData G k r),
      1 ≤ Fintype.card V → 1 ≤ k → 1 ≤ r → 1 ≤ d → 1 ≤ s → D.Holds d s →
      (100 * (d : ℝ) ^ 4 * Real.log (Fintype.card V) / s) ^ k < 1 / (r : ℝ) →
      HasCycleAtLeast G D.totalLength) ∧
    ∃ (P : List Instr) (K b : ℕ),
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k r d s : ℕ) (D : JoinData G k r),
        1 ≤ n → 1 ≤ k → 1 ≤ r → 1 ≤ d → 1 ≤ s → D.Holds d s →
        (100 * (d : ℝ) ^ 4 * Real.log n / s) ^ k < 1 / (r : ℝ) →
        ∀ (ω : Coins) (w : ℕ), WidthOK b (D.words d s) w →
          ∃ mem, exec P ω (K * G.edgeSet.ncard ^ 2) 0 0 (loadWords w (D.words d s)) = some mem ∧
            ∃ c : List (Fin n), IsCycleList G c ∧ D.totalLength ≤ c.length ∧
              OutputsWords mem (c.length :: c.map Fin.val) := by sorry

end PercCubeCycles
