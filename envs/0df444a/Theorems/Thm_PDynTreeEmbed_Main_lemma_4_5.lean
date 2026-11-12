-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_lemma_4_5
-- name    : PDynTreeEmbed.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:10.522277+00:00
-- url     : https://prove2.me/theorems/48cdb869-6942-4693-8dc7-0fa884a2b6c5
-- title:
--   Lemma 4.5 — dist(v, Center_ℓ(v)) ≤ F_ℓ(v) with E[F_ℓ(v)²] = O(r_ℓ(v)² D²) and E[F_ℓ(v)] = O(r_ℓ(v) D)
-- statement:
--   There is a universal constant $C$ such that the following holds. Fix a connected graph with integer weights in $[1,W]$ on $n\ge2$ vertices, a vertex $v$, a level $0<\ell<L$ with $D=2^\ell$, and a valid execution of Algorithm 2 with parameter $D$. Let $Q_w=E_{touch}(w,v)\cap\bigcap_{u\prec_\pi w}E_{cover}(u,v)^c$ and $F_\ell(v)=\max\{\mathrm{dist}_G(v,w):Q_w\text{ occurs}\}$, a function of the permutation and the radii only. Then on every outcome $\mathrm{dist}_G(v,\mathrm{Center}_\ell(v))\le F_\ell(v)$, and
--   $$\mathbb E[F_\ell(v)^2]\le C\,r_\ell(v)^2D^2,\qquad \mathbb E[\mathrm{dist}_G(v,\mathrm{Center}_\ell(v))]\le\mathbb E[F_\ell(v)]\le C\,r_\ell(v)\,D.$$
--
--   Differences from the source:
--
--   - encoding: a level 0 < ℓ < L with D = D_ℓ = 2^ℓ, L = ⌈log₂(nW)⌉ (§4.1) → hypotheses 0 < ℓ, ℓ < levels n W = Nat.clog 2 (n*W), D written 2^ℓ; reason: the section's fixed level made explicit
--   - reading: the output of Algorithm 2 ('compute X_i such that …', Blur's 'compute X_k such that …') → every valid execution: selectors X (function of π, R⃗) and Y (blur stage k of center w a function of π, R⃗ and r_{w,1..k}) satisfying (5), Algorithm 2 line 4 and Algorithm 3 line 5 (IsAlg2Exec); reason: a nondeterministic choice; quantifying over all choices is its meaning, and Lemmas 6.3/7.10 verify exactly these properties for the dynamic algorithms
--   - reading: for every outcome of the blur randomness → for every outcome in the support of the law: R_w ≥ 0 and r_{w,k} ∈ [0, α^{k−1}D/20] (IsOutcome); reason: outcomes outside the support have probability zero; on them (6) need not hold
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
--   - encoding: undirected graph G = (V, E, w), integral weights in [1, W], connected (standing assumptions, p. 13) → G : WGraph (Fin n) with ℕ weights, HasWeightsIn W (or HasPosWeights), G.adj.Connected; dist in ℕ ∪ {∞}; reason: the standing assumptions of §3 made explicit; distances are integers
--   - generalization: polynomially bounded weights W ≤ n^{O(1)} (standing assumption) → any W (the statement has no constant depending on W); reason: the bound W ≤ n^{c_W} is a special case
--   - encoding: O(r_ℓ(v)² D²) and O(r_ℓ(v) D) → an explicit universal constant C > 0, quantified before the graph, the level, the execution and the law; reason: the meaning of O(·)
--   - encoding: F_ℓ(v) depends on the permutation and the radii at level ℓ only → farCenter is a function of (π, R⃗) by its type; reason: the clause holds by construction
--   - encoding: F_ℓ(v) = max over the w with Q_w → farCenter = 0 when no Q_w occurs; reason: Q_w occurs for the first toucher in π order on every outcome in the support, so the max is never empty there
--   - encoding: π uniform, R_w ∼ Exp(1/D) i.i.d. (rate 1/D, mean D) per vertex, blur radii r_{w,k} ∼ Unif[0, α^{k−1}σ], all independent → any probability space with a random outcome ζ satisfying IsAlg2Law (laws via Measure.map, iIndepFun, IndepFun); reason: a statement about every realization of the law is the statement about the law
--   - encoding: the expectation of a quantity depending on the algorithm's output → the blur selectors are measurable (IsMeasurableExec), assumed only in the expectation clauses; expectations as lintegrals in [0, ∞]; reason: a randomized algorithm's output is a random variable; without measurability the lintegral would be a lower integral
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 16, Lemma 4.5

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Static
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Lemma 4.5** (Distance to the center, p. 16). There is a universal constant `C` such that, for
a connected graph on `n ≥ 2` vertices with integer weights in `[1, W]`, a vertex `v`, a level
`0 < ℓ < L = ⌈log₂(nW)⌉`, `D = 2^ℓ`, and a valid execution of Algorithm 2 with parameter `D`:
`F_ℓ(v) = max{dist_G(v, w) : Q_w occurs}` (a function of `π` and the radii only) satisfies, on every
outcome, `dist_G(v, Center_ℓ(v)) ≤ F_ℓ(v)`; and `E[F_ℓ(v)²] ≤ C·r_ℓ(v)²·D²`,
`E[dist_G(v, Center_ℓ(v))] ≤ E[F_ℓ(v)] ≤ C·r_ℓ(v)·D`. -/
theorem lemma_4_5 : ∃ C : ℝ, 0 < C ∧
    ∀ (n W ℓ : ℕ) (G : WGraph (Fin n)), 2 ≤ n → G.adj.Connected → G.HasWeightsIn W → 0 < ℓ →
      ℓ < levels n W →
      ∀ (X : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → Finset (Fin n))
        (Y : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n)),
        IsAlg2Exec G (2 ^ ℓ) X Y → ∀ v : Fin n,
        (∀ ζ : Outcome n, IsOutcome ((2 : ℝ) ^ ℓ) ζ →
          (G.dist v (center Y (2 ^ ℓ) ζ v)).toNat ≤ farCenter G (2 ^ ℓ) ζ.1 ζ.2.1 v) ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (ζ : Ω → Outcome n),
          IsAlg2Law P n (2 ^ ℓ) ζ → IsMeasurableExec Y →
          ∫⁻ ω, (farCenter G (2 ^ ℓ) (ζ ω).1 (ζ ω).2.1 v : ℝ≥0∞) ^ 2 ∂P ≤
              ENNReal.ofReal (C * profile G v ℓ ^ 2 * ((2 : ℝ) ^ ℓ) ^ 2) ∧
            ∫⁻ ω, ((G.dist v (center Y (2 ^ ℓ) (ζ ω) v)).toNat : ℝ≥0∞) ∂P ≤
              ∫⁻ ω, (farCenter G (2 ^ ℓ) (ζ ω).1 (ζ ω).2.1 v : ℝ≥0∞) ∂P ∧
            ∫⁻ ω, (farCenter G (2 ^ ℓ) (ζ ω).1 (ζ ω).2.1 v : ℝ≥0∞) ∂P ≤
              ENNReal.ofReal (C * profile G v ℓ * (2 : ℝ) ^ ℓ) := by sorry

end PDynTreeEmbed.Main
