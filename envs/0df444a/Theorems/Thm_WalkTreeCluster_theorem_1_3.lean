-- Prove2me | Theorems.Thm_WalkTreeCluster_theorem_1_3
-- name    : WalkTreeCluster.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:45:21.400505+00:00
-- url     : https://prove2.me/theorems/7cbebfe7-b14d-4034-b956-9fb3b5ffd7c5
-- title:
--   Theorem 1.3: a pair classifier with expected time $C_0(\epsilon^{-1}\phi^{-1})^{C_0}r^{1/2+C_0\log\log(\phi^2/\epsilon)/\log(\phi^2/\epsilon)}$
-- statement:
--   There are absolute constants $c_0\in(0,1/4)$ and $C_0\ge1$ and a randomized algorithm with the following guarantee. Let $n\ge2$, $d\ge1$, $0<\phi\le1$ and $0<\epsilon\le c_0\phi^2$, let $G$ be an undirected $d$-regular graph on $n$ vertices and $\mathcal C$ a family of clusters (Definition 1.2), and write $S=\bigcup_{C\in\mathcal C}C$. The algorithm is given $n,d,\epsilon,\phi$ and neighbor-query access to $G$, and uses no preprocessing.
--
--   There is a set $B\subseteq V$ with
--   $$|B\cap C|\le C_0(\epsilon/\phi^2)^{1/50}|C|\quad(C\in\mathcal C),\qquad|B|\le C_0(\epsilon/\phi^2)^{1/1000}|S|,$$
--   such that for every pair $u,v\in V\setminus B$ with $\{u,v\}\cap S\ne\emptyset$:
--   1. the algorithm decides correctly whether $u$ and $v$ belong to the same cluster with probability at least $0.9$;
--   2. with $r=\min\{|C|:C\in\mathcal C,\ C\cap\{u,v\}\ne\emptyset\}$, its expected number of graph queries and its expected running time are at most
--   $$C_0(\epsilon^{-1}\phi^{-1})^{C_0}\,r^{\frac12+C_0\frac{\log\log(\phi^2/\epsilon)}{\log(\phi^2/\epsilon)}} .$$
--
--   This is the main result of the paper: a same-cluster oracle for clusters of arbitrary size in arbitrary noise, in time nearly the square root of the cluster size.
--
--   **Formalization Note.** The algorithm is an admissible program of the randomized neighbor-query real RAM of the mission, chosen before $n,d,\epsilon,\phi$, the graph and the clusters; its input is $(n,d,u,v,\epsilon,\phi)$ and *accept* means "same cluster". Correctness is required for every pair, including $u=v$.
--
--   Differences from the source:
--   - reading: a randomized algorithm, charged per Section 10.1 (unit cost for arithmetic, scalar evaluations, random choices, operations on vertex identifiers and neighbor indices; a neighbor query in O(1)) → an admissible program (rational literals) of WalkTreeCluster.Machine: the SmaleNinth real-RAM core plus integer pointer ±, integer memory, pointer-to-real, rpow, a fair coin, a uniform index choice and the charged neighbor query; one unit of work per instruction; reason: the page names no machine; rpow and the uniform index are its unit-cost scalar evaluations and random choices, and nothing stronger (no floor, log, exp, biased coin) is added
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: the algorithm is given n, d, ϵ, ϕ (and the queried pair u, v) and outputs same/different → integer memory I0 = n, I1 = d, I2 = u, I3 = v; real memory 0 = ϵ, 1 = ϕ; accept = same, reject = different; reason: input/output layout of the machine
--   - encoding: probability at least 0.9 over the randomness of the query → a measurable set of tapes of probability ≥ 9/10 on which the run halts with the correct answer; reason: inner-measure form; it implies the probability of the (possibly non-measurable) success event is at least 0.9
--   - encoding: expected number of queries and expected running time → a measurable g ≥ the count (in ℕ∞, ⊤ for an unbounded run) with ∫⁻ g ≤ bound; reason: upper-integral form; it is the page's expectation bound for a measurable count and never weaker
--   - encoding: bound evaluated at r = min{|C| : C ∈ 𝒞, C ∩ {u, v} ≠ ∅} → bound evaluated at |C| for every C ∈ 𝒞 that meets {u, v}; reason: the exponent is positive on the parameter range (proved in the sanity files), so the bound is nondecreasing in |C| and the two forms agree
--   - encoding: the randomness of the algorithm → one tape of independent uniform [0, 1] values (Measure.infinitePi); reason: a single source of randomness for the machine's coin and index choice
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Theorem 1.3, p.2 (restated p.74)

import Mathlib
import Definitions.Def_WalkTreeCluster_Graph
import Definitions.Def_WalkTreeCluster_Machine

open scoped Classical
open MeasureTheory

namespace WalkTreeCluster

/-- **Theorem 1.3** (Pair classifier), p.2 (PDF p.5; restated p.74). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

There are absolute constants `c₀ ∈ (0, 1/4)` and `C₀ ≥ 1` and a randomized algorithm with the
following guarantee. Let `n ≥ 2`, `d ≥ 1`, `0 < ϕ ≤ 1`, and `0 < ϵ ≤ c₀ϕ²`. Let `G` and `𝒞` satisfy
Definition 1.2, and write `S = ⋃_{C ∈ 𝒞} C`. The algorithm is given `n, d, ϵ, ϕ` and neighbor-query
access to `G`, and uses no preprocessing. There exists a set `B ⊆ V` such that
`|B ∩ C| ≤ C₀(ϵ/ϕ²)^{1/50}|C|` for every `C ∈ 𝒞` and `|B| ≤ C₀(ϵ/ϕ²)^{1/1000}|S|`. For each pair
`u, v ∈ V ∖ B` with `{u, v} ∩ S ≠ ∅`, the algorithm correctly decides whether `u` and `v` belong to
the same cluster with probability at least `0.9`. Writing `r = min{|C| : C ∈ 𝒞, C ∩ {u, v} ≠ ∅}`,
its expected number of graph queries and expected running time are at most
`C₀(ϵ⁻¹ϕ⁻¹)^{C₀} r^{1/2 + C₀ log log(ϕ²/ϵ)/log(ϕ²/ϵ)}`.

**Formalization Note.**
* "A randomized algorithm" is an admissible program of the machine `WalkTreeCluster.Machine`
  (rational literals; the graph is read only through charged neighbor queries; unit cost per
  instruction), chosen before `n, d, ϵ, ϕ`, the graph and the clusters. Its input is
  `(n, d, u, v, ϵ, ϕ)`; output `true` (core `accept`) means "same cluster".
* The graph is a neighbor-list graph on `Fin n` (undirected, no parallel edges, loops allowed).
* "Probability at least 0.9" is: some measurable set of tapes of probability at least `0.9` on
  which the run halts with the correct answer (an inner-measure bound). "Expected … at most" is:
  some measurable `g` dominating the count (in `ℕ∞ ⊆ ℝ≥0∞`, `⊤` for an unbounded run) has
  integral at most the bound (an upper-integral bound).
* "`≤ bound(r)` with `r` the least size of a cluster meeting `{u, v}`" is stated as
  "`≤ bound(|C|)` for every cluster `C` meeting `{u, v}`"; the two agree since the exponent is
  positive on the parameter range. -/
theorem theorem_1_3 :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 < 1 / 4 ∧ ∃ C0 : ℝ, 1 ≤ C0 ∧ ∃ P : Program, Admissible P ∧
    ∀ (n d : ℕ), 2 ≤ n → 1 ≤ d → ∀ ϕ ϵ : ℝ, 0 < ϕ → ϕ ≤ 1 → 0 < ϵ → ϵ ≤ c0 * ϕ ^ 2 →
    ∀ nbr : Fin n → Fin d → Fin n, IsUndirected nbr → NoParallel nbr →
    ∀ 𝒞 : Finset (Finset (Fin n)), IsClusterFamily nbr ϵ ϕ 𝒞 →
    ∃ B : Finset (Fin n),
      (∀ C ∈ 𝒞, ((B ∩ C).card : ℝ) ≤ C0 * (ϵ / ϕ ^ 2) ^ (1 / 50 : ℝ) * C.card) ∧
      ((B.card : ℝ) ≤ C0 * (ϵ / ϕ ^ 2) ^ (1 / 1000 : ℝ) * (clusterUnion 𝒞).card) ∧
      ∀ u v : Fin n, u ∉ B → v ∉ B → (u ∈ clusterUnion 𝒞 ∨ v ∈ clusterUnion 𝒞) →
        (∃ E : Set (ℕ → ℝ), MeasurableSet E ∧
          E ⊆ {ω | HaltsWith P nbr ω (input n d u v ϵ ϕ) (decide (∃ C ∈ 𝒞, u ∈ C ∧ v ∈ C))} ∧
          (9 / 10 : ENNReal) ≤ tape E) ∧
        ∀ C ∈ 𝒞, (u ∈ C ∨ v ∈ C) →
          (∃ g : (ℕ → ℝ) → ENNReal, Measurable g ∧
            (∀ ω, ((totalQueries P nbr ω (input n d u v ϵ ϕ) : ℕ∞) : ENNReal) ≤ g ω) ∧
            ∫⁻ ω, g ω ∂tape ≤ ENNReal.ofReal (C0 * (ϵ⁻¹ * ϕ⁻¹) ^ C0 * (C.card : ℝ) ^
              (1 / 2 + C0 * Real.log (Real.log (ϕ ^ 2 / ϵ)) / Real.log (ϕ ^ 2 / ϵ)))) ∧
          (∃ g : (ℕ → ℝ) → ENNReal, Measurable g ∧
            (∀ ω, ((totalWork P nbr ω (input n d u v ϵ ϕ) : ℕ∞) : ENNReal) ≤ g ω) ∧
            ∫⁻ ω, g ω ∂tape ≤ ENNReal.ofReal (C0 * (ϵ⁻¹ * ϕ⁻¹) ^ C0 * (C.card : ℝ) ^
              (1 / 2 + C0 * Real.log (Real.log (ϕ ^ 2 / ϵ)) / Real.log (ϕ ^ 2 / ϵ)))) := by sorry

end WalkTreeCluster
