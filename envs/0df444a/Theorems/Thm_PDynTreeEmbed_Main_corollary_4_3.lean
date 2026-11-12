-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_corollary_4_3
-- name    : PDynTreeEmbed.Main.corollary_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:14.911193+00:00
-- url     : https://prove2.me/theorems/11219bc5-4fc4-4a21-8bf4-13cf99c32a09
-- title:
--   Corollary 4.3 — the center of v touches v and no earlier center covers v
-- statement:
--   Fix a connected graph with integer weights in $[1,W]$ on $n\ge2$ vertices, a level $0<\ell<L$ with $D=2^\ell$, and a valid execution of Algorithm 2 with parameter $D$. On every outcome, if $\mathrm{Center}_\ell(v)=w$, then
--   $$E_{touch}(w,v)\ \text{occurs, and}\ E_{cover}(u,v)\ \text{occurs for no}\ u\prec_\pi w.$$
--   It reduces the distance from a vertex to its center to the radii alone.
--
--   Differences from the source:
--
--   - encoding: a level 0 < ℓ < L with D = D_ℓ = 2^ℓ, L = ⌈log₂(nW)⌉ (§4.1) → hypotheses 0 < ℓ, ℓ < levels n W = Nat.clog 2 (n*W), D written 2^ℓ; reason: the section's fixed level made explicit
--   - reading: the output of Algorithm 2 ('compute X_i such that …', Blur's 'compute X_k such that …') → every valid execution: selectors X (function of π, R⃗) and Y (blur stage k of center w a function of π, R⃗ and r_{w,1..k}) satisfying (5), Algorithm 2 line 4 and Algorithm 3 line 5 (IsAlg2Exec); reason: a nondeterministic choice; quantifying over all choices is its meaning, and Lemmas 6.3/7.10 verify exactly these properties for the dynamic algorithms
--   - reading: for every outcome of the blur randomness → for every outcome in the support of the law: R_w ≥ 0 and r_{w,k} ∈ [0, α^{k−1}D/20] (IsOutcome); reason: outcomes outside the support have probability zero; on them (6) need not hold
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
--   - encoding: undirected graph G = (V, E, w), integral weights in [1, W], connected (standing assumptions, p. 13) → G : WGraph (Fin n) with ℕ weights, HasWeightsIn W (or HasPosWeights), G.adj.Connected; dist in ℕ ∪ {∞}; reason: the standing assumptions of §3 made explicit; distances are integers
--   - generalization: polynomially bounded weights W ≤ n^{O(1)} (standing assumption) → any W (the statement has no constant depending on W); reason: the bound W ≤ n^{c_W} is a special case
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 15, Corollary 4.3

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Static

namespace PDynTreeEmbed.Main

/-- **Corollary 4.3** (p. 15). Fix a connected graph on `n ≥ 2` vertices with integer weights in
`[1, W]`, a level `0 < ℓ < L = ⌈log₂(nW)⌉`, `D = 2^ℓ`, and a valid execution of Algorithm 2 with
parameter `D`. On every outcome of the randomness, if `Center_ℓ(v) = w`, then the center `w`
touches `v`, and no center `u ≺_π w` covers `v`. -/
theorem corollary_4_3 (n W ℓ : ℕ) (G : WGraph (Fin n)) (hn : 2 ≤ n) (hconn : G.adj.Connected)
    (hW : G.HasWeightsIn W) (hℓ : 0 < ℓ) (hℓL : ℓ < levels n W)
    (X : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → Finset (Fin n))
    (Y : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n))
    (hexec : IsAlg2Exec G (2 ^ ℓ) X Y) (ζ : Outcome n) (hζ : IsOutcome ((2 : ℝ) ^ ℓ) ζ)
    (v w : Fin n) (hc : center Y (2 ^ ℓ) ζ v = w) :
    Touches G (2 ^ ℓ) ζ.2.1 w {v} ∧
      ∀ u, ζ.1.symm u < ζ.1.symm w → ¬ Covers G (2 ^ ℓ) ζ.2.1 u {v} := by sorry

end PDynTreeEmbed.Main
