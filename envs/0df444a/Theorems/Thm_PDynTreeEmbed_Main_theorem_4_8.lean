-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_theorem_4_8
-- name    : PDynTreeEmbed.Main.theorem_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:21.297694+00:00
-- url     : https://prove2.me/theorems/aab5ef9e-593c-4c7e-afd6-97e11d8bb982
-- title:
--   Theorem 4.8 — the tree T of §4.4 is an O(log n)-approximate probabilistic tree embedding
-- statement:
--   For every weight exponent $c_W$ there is $C$ such that the following holds. Let $G$ be a connected graph on $n\ge2$ vertices with integer weights in $[1,W]$, $W\le n^{c_W}$, $L=\lceil\log_2(nW)\rceil$, $c^\star$ a vertex, and for each level $0<\ell<L$ a valid execution of Algorithm 2 with $D_\ell=2^\ell$, the levels using independent randomness. Then the tree $T$ of §4.4 is an $O(\log n)$-approximate probabilistic tree embedding of $G$: on every outcome $T$ is a tree containing the leaves $V$ and $\mathrm{dist}_T(u,v)\ge\mathrm{dist}_G(u,v)$, and
--   $$\mathbb E[\mathrm{dist}_T(u,v)]\le C\log_2 n\cdot\mathrm{dist}_G(u,v)\qquad\text{for all }u,v\in V.$$
--   It is the static result the dynamic tree of Theorem 1.2 maintains.
--
--   Differences from the source:
--
--   - encoding: a distribution over trees T with V ⊆ V(T); dist_T ≥ dist_G for every T ∈ supp → on every outcome: hierTree is a tree on treeNodes, the leaf (0, {v}) stands for v, and dist_T ≥ dist_G; reason: the tree is built on every outcome, so 'every T in the support' is every outcome
--   - encoding: O(log n)-approximate → ∀ c_W ∃ C > 0 with E[dist_T(u, v)] ≤ C·log₂ n·dist_G(u, v), W ≤ n^{c_W}; reason: the O(log n) of Claim 4.4(i) depends on the weight exponent
--   - encoding: C_ℓ for 0 < ℓ < L computed by Algorithm 2 independently for each level; C_0 singletons; C_L = {V} with center c⋆ → per-level valid measurable executions (Xs ℓ, Ys ℓ) and outcomes ζ ℓ with IsAlg2Law at D = 2^ℓ, iIndepFun across the levels 0 < ℓ < L; levelCenters; reason: the construction of p. 13 and §4.4
--   - reading: the output of Algorithm 2 ('compute X_i such that …', Blur's 'compute X_k such that …') → every valid execution: selectors X (function of π, R⃗) and Y (blur stage k of center w a function of π, R⃗ and r_{w,1..k}) satisfying (5), Algorithm 2 line 4 and Algorithm 3 line 5 (IsAlg2Exec); reason: a nondeterministic choice; quantifying over all choices is its meaning, and Lemmas 6.3/7.10 verify exactly these properties for the dynamic algorithms
--   - encoding: the expectation of a quantity depending on the algorithm's output → the blur selectors are measurable (IsMeasurableExec), assumed only in the expectation clauses; expectations as lintegrals in [0, ∞]; reason: a randomized algorithm's output is a random variable; without measurability the lintegral would be a lower integral
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
--   - encoding: undirected graph G = (V, E, w), integral weights in [1, W], connected (standing assumptions, p. 13) → G : WGraph (Fin n) with ℕ weights, HasWeightsIn W (or HasPosWeights), G.adj.Connected; dist in ℕ ∪ {∞}; reason: the standing assumptions of §3 made explicit; distances are integers
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 19, Theorem 4.8

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Static
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Theorem 4.8** (Tight tree embedding, p. 19). For every weight exponent `c_W` there is `C` such
that the following holds. Let `G` be a connected graph on `n ≥ 2` vertices with integer weights in
`[1, W]`, `W ≤ n^{c_W}`, `L = ⌈log₂(nW)⌉`, `c⋆` a vertex, and for each level `0 < ℓ < L` a valid
execution of Algorithm 2 with `D_ℓ = 2^ℓ`, run on independent randomness. Then the tree `T` of §4.4
is an `O(log n)`-approximate probabilistic tree embedding of `G`: on every outcome `T` is a tree
whose leaves are identified with `V` and `dist_T(u, v) ≥ dist_G(u, v)`, and
`E[dist_T(u, v)] ≤ C·log₂ n·dist_G(u, v)` for all `u, v`. -/
theorem theorem_4_8 : ∀ cW : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ (n W : ℕ) (G : WGraph (Fin n)), 2 ≤ n → (W : ℝ) ≤ (n : ℝ) ^ cW → G.adj.Connected →
      G.HasWeightsIn W → ∀ (cstar : Fin n)
      (Xs : ℕ → Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → Finset (Fin n))
      (Ys : ℕ → Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n)),
      (∀ ℓ, 0 < ℓ → ℓ < levels n W →
        IsAlg2Exec G (2 ^ ℓ) (Xs ℓ) (Ys ℓ) ∧ IsMeasurableExec (Ys ℓ)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ζ : ℕ → Ω → Outcome n),
        (∀ ℓ, 0 < ℓ → ℓ < levels n W → IsAlg2Law P n (2 ^ ℓ) (ζ ℓ)) →
        iIndepFun (fun ℓ : {ℓ : ℕ // 0 < ℓ ∧ ℓ < levels n W} => ζ ℓ.1) P →
        (∀ ω, (hierTree G (levels n W) (levelCenters (levels n W) cstar Ys fun ℓ => ζ ℓ ω)).IsTreeOn
            (treeNodes (levels n W) (levelCenters (levels n W) cstar Ys fun ℓ => ζ ℓ ω)) ∧
          ∀ u v : Fin n, G.dist u v ≤
            (hierTree G (levels n W) (levelCenters (levels n W) cstar Ys fun ℓ => ζ ℓ ω)).dist
              (leaf (levels n W) (levelCenters (levels n W) cstar Ys fun ℓ => ζ ℓ ω) u)
              (leaf (levels n W) (levelCenters (levels n W) cstar Ys fun ℓ => ζ ℓ ω) v)) ∧
        ∀ u v : Fin n,
          ∫⁻ ω, ((hierTree G (levels n W) (levelCenters (levels n W) cstar Ys fun ℓ => ζ ℓ ω)).dist
              (leaf (levels n W) (levelCenters (levels n W) cstar Ys fun ℓ => ζ ℓ ω) u)
              (leaf (levels n W) (levelCenters (levels n W) cstar Ys fun ℓ => ζ ℓ ω) v) : ℝ≥0∞) ∂P ≤
            ENNReal.ofReal (C * log2 n) * (G.dist u v : ℝ≥0∞) := by sorry

end PDynTreeEmbed.Main
