-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_theorem_2_2
-- name    : PDynTreeEmbed.Main.theorem_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:16.109333+00:00
-- url     : https://prove2.me/theorems/770024c5-147b-4add-bdde-1b8f974103b9
-- title:
--   Theorem 2.2 — blurry ball growing [BEL20]: cut probability O(w(e)/σ), growth at most σ/(1 − α), O(log n) stages
-- statement:
--   Let $G$ be a connected graph on $n\ge2$ vertices with positive integer weights, $\alpha=1/(2\log_2 n)$, $\sigma>0$ and $X\subseteq V$. Every valid execution of $\mathrm{Blur}(G,\sigma,X)$ (Algorithm 3: $K=\max(0,\lfloor\log\sigma/\log(1/\alpha)\rfloor+1)$ stages, each a $(1+\alpha^2)$-approximate ball growth with radius $r_k\sim\mathrm{Unif}[0,\alpha^{k-1}\sigma]$) outputs a superset $U$ of $X$ with
--   $$\Pr\big[e\in E(U,V\setminus U)\big]\le C\,\frac{w(e)}{\sigma}\quad\text{for every edge }e,\qquad \mathrm{dist}_G(X,v)\le\frac{\sigma}{1-\alpha}\quad\text{for every }v\in U,$$
--   for a universal constant $C$, and it uses $K$ approximate SSSP computations, with $K\le C'\log_2 n$ whenever $\sigma\le n^c$ ($C'$ depending on $c$ only). It turns approximate balls into cuts with exact-ball separation guarantees.
--
--   Differences from the source:
--
--   - reading: there is a routine Blur(G, σ, X) computing U with O(log n) calls to a (1 + α²)-approximate SSSP algorithm → every valid execution of Algorithm 3 (IsBlurRun: B(X_{k−1}, r_k/(1+α²)) ⊆ X_k ⊆ B(X_{k−1}, r_k), stage k depending only on r_1..r_k); reason: p. 10: Algorithm 3 is the routine of [BEL20] and its output satisfies Theorem 2.2; every approximate SSSP call is one such choice
--   - encoding: K = ⌊log σ / log(1/α)⌋ + 1 → blurK n σ = max(0, ⌊log σ / log(1/α)⌋ + 1); reason: for σ < 1 no stage is run (p. 24)
--   - reading: O(log n) calls → ∀ c, ∃ C', K ≤ C'·log₂ n whenever 0 < σ ≤ n^c; reason: K is O(log n) exactly for polynomially bounded σ; the paper uses σ = D/20 < 2^L/20 ≤ nW
--   - encoding: first guarantee as a probability → the probability of the cut event under IsBlurLaw (independent r_k ∼ Unif[0, α^{k−1}σ] on any probability space), for executions whose stage-membership events {r | v ∈ Y r k} are measurable; reason: a randomized routine's output is a random variable: Algorithm 3 run with a deterministic SSSP routine has measurable stages, so the routine the theorem asserts still qualifies; without the hypothesis the bound would be on an outer measure, which a non-measurable selector can inflate
--   - encoding: the containment and distance guarantees → for every radius vector in the support (r_k ∈ [0, α^{k−1}σ]); reason: outside the support the radii are not those of the algorithm
--   - encoding: O(w(e)/σ) → an explicit universal constant C > 0, quantified before the graph, the level, the execution and the law; reason: the meaning of O(·)
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
--   - encoding: the input graph (standing assumptions: connected, positive integer weights) → G.adj.Connected, HasPosWeights; reason: the standing assumptions of p. 13
--   - generalization: polynomially bounded weights W ≤ n^{O(1)} (standing assumption) → any W (the statement has no constant depending on W); reason: the bound W ≤ n^{c_W} is a special case
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 8, Theorem 2.2 (with Algorithm 3, p. 10)

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Static
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Theorem 2.2** ([BEL20], p. 8), for the routine Blur of Algorithm 3 (p. 10). Let `α = 1/(2 log₂ n)`.
For every connected graph on `n ≥ 2` vertices with positive integer weights, every `σ > 0`, every
set `X` and every valid execution of `Blur(G, σ, X)` (stages `K = max(0, ⌊log σ/log(1/α)⌋ + 1)`,
stage radii `r_k ∼ Unif[0, α^{k−1}σ]` independent): the output `U` is a superset of `X`; every
`v ∈ U` satisfies `d_G(X, v) ≤ σ/(1 − α)`; and every edge `e` lies in `E(U, V ∖ U)` with
probability at most `C·w(e)/σ`, for a universal constant `C`, whenever the execution's stage
membership events are measurable in the blur radii. Moreover the number `K` of
`(1 + α²)`-approximate SSSP computations is `O(log n)`: for every `c` there is `C'` with
`K ≤ C'·log₂ n` whenever `σ ≤ n^c`. -/
theorem theorem_2_2 :
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : WGraph (Fin n)), 2 ≤ n → G.adj.Connected →
      G.HasPosWeights → ∀ (σ : ℝ), 0 < σ → ∀ (X : Finset (Fin n))
        (Y : (ℕ → ℝ) → ℕ → Finset (Fin n)), IsBlurRun G σ X Y →
        (∀ r : ℕ → ℝ, (∀ k, 0 ≤ r k ∧ r k ≤ blurAlpha n ^ k * σ) →
          X ⊆ Y r (blurK n σ) ∧
            ∀ v ∈ Y r (blurK n σ), ((G.distFrom X v).toNat : ℝ) ≤ σ / (1 - blurAlpha n)) ∧
        ((∀ k (v : Fin n), MeasurableSet {r : ℕ → ℝ | v ∈ Y r k}) →
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (r : Ω → ℕ → ℝ), IsBlurLaw P n σ r →
          ∀ e ∈ G.adj.edgeSet,
            P {ω | e ∈ G.edgesBetween (Y (r ω) (blurK n σ) : Set (Fin n))
                (Y (r ω) (blurK n σ) : Set (Fin n))ᶜ} ≤
              ENNReal.ofReal (C * (G.wt e : ℝ) / σ))) ∧
    ∀ c : ℝ, ∃ C' : ℝ, ∀ (n : ℕ) (σ : ℝ), 2 ≤ n → 0 < σ → σ ≤ (n : ℝ) ^ c →
      (blurK n σ : ℝ) ≤ C' * log2 n := by sorry

end PDynTreeEmbed.Main
