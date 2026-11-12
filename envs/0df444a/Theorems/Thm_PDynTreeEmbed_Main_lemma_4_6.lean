-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_lemma_4_6
-- name    : PDynTreeEmbed.Main.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:15.453389+00:00
-- url     : https://prove2.me/theorems/66667b93-a5b6-4240-99b1-ee4f89901fe3
-- title:
--   Lemma 4.6 — an edge is cut with probability O(w(e)/D_ℓ), and E[1{cut}·dist(z, Center_ℓ(z))] = O(w(e) r_ℓ(z))
-- statement:
--   There is a universal constant $C$ such that the following holds. Fix a connected graph with integer weights in $[1,W]$ on $n\ge2$ vertices, a level $0<\ell<L$ at a scale $D_\ell=2^\ell\ge20$, and a valid execution of Algorithm 2 with parameter $D_\ell$. For every edge $e=(u,v)$ and either endpoint $z\in\{u,v\}$,
--   $$\Pr[\mathcal C_\ell(u)\ne\mathcal C_\ell(v)]\le C\,\frac{w(e)}{D_\ell},\qquad \mathbb E\big[\mathbf 1\{\mathcal C_\ell(u)\ne\mathcal C_\ell(v)\}\,\mathrm{dist}_G(z,\mathrm{Center}_\ell(z))\big]\le C\,w(e)\,r_\ell(z).$$
--
--   Differences from the source:
--
--   - encoding: a level 0 < ℓ < L with D = D_ℓ = 2^ℓ, L = ⌈log₂(nW)⌉ (§4.1) → hypotheses 0 < ℓ, ℓ < levels n W = Nat.clog 2 (n*W), D written 2^ℓ; reason: the section's fixed level made explicit
--   - reading: the output of Algorithm 2 ('compute X_i such that …', Blur's 'compute X_k such that …') → every valid execution: selectors X (function of π, R⃗) and Y (blur stage k of center w a function of π, R⃗ and r_{w,1..k}) satisfying (5), Algorithm 2 line 4 and Algorithm 3 line 5 (IsAlg2Exec); reason: a nondeterministic choice; quantifying over all choices is its meaning, and Lemmas 6.3/7.10 verify exactly these properties for the dynamic algorithms
--   - reading: for every outcome of the blur randomness → for every outcome in the support of the law: R_w ≥ 0 and r_{w,k} ∈ [0, α^{k−1}D/20] (IsOutcome); reason: outcomes outside the support have probability zero; on them (6) need not hold
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
--   - encoding: undirected graph G = (V, E, w), integral weights in [1, W], connected (standing assumptions, p. 13) → G : WGraph (Fin n) with ℕ weights, HasWeightsIn W (or HasPosWeights), G.adj.Connected; dist in ℕ ∪ {∞}; reason: the standing assumptions of §3 made explicit; distances are integers
--   - generalization: polynomially bounded weights W ≤ n^{O(1)} (standing assumption) → any W (the statement has no constant depending on W); reason: the bound W ≤ n^{c_W} is a special case
--   - encoding: O(w(e)/D_ℓ) and O(w(e) r_ℓ(z)) → an explicit universal constant C > 0, quantified before the graph, the level, the execution and the law; reason: the meaning of O(·)
--   - encoding: C_ℓ(u) ≠ C_ℓ(v) → Center_ℓ(u) ≠ Center_ℓ(v); reason: clusters are the classes of Center (C_i = U_i ∖ ⋃_{j<i} C_j)
--   - encoding: scale D_ℓ ≥ 20 → hypothesis (20 : ℝ) ≤ 2^ℓ; reason: literal
--   - encoding: π uniform, R_w ∼ Exp(1/D) i.i.d. (rate 1/D, mean D) per vertex, blur radii r_{w,k} ∼ Unif[0, α^{k−1}σ], all independent → any probability space with a random outcome ζ satisfying IsAlg2Law (laws via Measure.map, iIndepFun, IndepFun); reason: a statement about every realization of the law is the statement about the law
--   - encoding: the expectation of a quantity depending on the algorithm's output → the blur selectors are measurable (IsMeasurableExec), assumed only in the expectation clauses; expectations as lintegrals in [0, ∞]; reason: a randomized algorithm's output is a random variable; without measurability the lintegral would be a lower integral
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 17, Lemma 4.6

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Static
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Lemma 4.6** (Weighted cut bound, p. 17). There is a universal constant `C` such that, for a
connected graph on `n ≥ 2` vertices with integer weights in `[1, W]`, a level `0 < ℓ < L` at a
scale `D_ℓ = 2^ℓ ≥ 20`, a valid execution of Algorithm 2 with parameter `D_ℓ`, every edge
`e = (u, v)` and either endpoint `z ∈ {u, v}`: `P[C_ℓ(u) ≠ C_ℓ(v)] ≤ C·w(e)/D_ℓ` and
`E[1{C_ℓ(u) ≠ C_ℓ(v)}·dist_G(z, Center_ℓ(z))] ≤ C·w(e)·r_ℓ(z)`. -/
theorem lemma_4_6 : ∃ C : ℝ, 0 < C ∧
    ∀ (n W ℓ : ℕ) (G : WGraph (Fin n)), 2 ≤ n → G.adj.Connected → G.HasWeightsIn W → 0 < ℓ →
      ℓ < levels n W → (20 : ℝ) ≤ 2 ^ ℓ →
      ∀ (X : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → Finset (Fin n))
        (Y : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n)),
        IsAlg2Exec G (2 ^ ℓ) X Y →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (ζ : Ω → Outcome n),
          IsAlg2Law P n (2 ^ ℓ) ζ → IsMeasurableExec Y →
          ∀ u v : Fin n, G.adj.Adj u v → ∀ z : Fin n, (z = u ∨ z = v) →
            P {ω | center Y (2 ^ ℓ) (ζ ω) u ≠ center Y (2 ^ ℓ) (ζ ω) v} ≤
                ENNReal.ofReal (C * (G.wt s(u, v) : ℝ) / (2 : ℝ) ^ ℓ) ∧
              ∫⁻ ω, (if center Y (2 ^ ℓ) (ζ ω) u ≠ center Y (2 ^ ℓ) (ζ ω) v then
                  ((G.dist z (center Y (2 ^ ℓ) (ζ ω) z)).toNat : ℝ≥0∞) else 0) ∂P ≤
                ENNReal.ofReal (C * (G.wt s(u, v) : ℝ) * profile G z ℓ) := by sorry

end PDynTreeEmbed.Main
