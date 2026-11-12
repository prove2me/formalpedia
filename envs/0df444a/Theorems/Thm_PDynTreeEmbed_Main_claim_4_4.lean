-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_claim_4_4
-- name    : PDynTreeEmbed.Main.claim_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:13.295083+00:00
-- url     : https://prove2.me/theorems/81c9f318-638b-44f5-84a6-fa0cd14e1a93
-- title:
--   Claim 4.4 — the ball-growth profile [KPGR25]: Σ_ℓ r_ℓ(v) = O(log n) and |B(v,(r_ℓ+h)2^ℓ)| ≤ e^{h/2}|B(v,r_ℓ 2^ℓ)|
-- statement:
--   For every vertex $v$ of a connected graph with integer weights in $[1,W]$ on $n\ge2$ vertices, the profile (7)–(8) satisfies
--
--   (i) $\displaystyle\sum_{\ell=0}^{L}r_\ell(v)=O(\log n)$, with $L=\lceil\log_2(nW)\rceil$: for every $c_W$ there is $C$ with $\sum_{\ell=0}^{L}r_\ell(v)\le C\log_2 n$ whenever $W\le n^{c_W}$;
--
--   (ii) for every level $\ell\ge1$ and every integer $h\ge1$,
--   $$\big|B_G\big(v,(r_\ell(v)+h)2^\ell\big)\big|\le e^{h/2}\,\big|B_G\big(v,r_\ell(v)2^\ell\big)\big|.$$
--   The profile is what makes the stretch $O(\log n)$ rather than $O(\log^2 n)$.
--
--   Differences from the source:
--
--   - encoding: (i) O(log n) under polynomially bounded weights → ∀ c_W, ∃ C > 0, ∀ graphs with W ≤ n^{c_W}: Σ_{ℓ ≤ L} r_ℓ(v) ≤ C·log₂ n; reason: the sum has L + 1 terms with L = ⌈log₂(nW)⌉, which is O(log n) only through W ≤ n^{c_W}; C depends on c_W
--   - generalization: (ii) under the standing assumption of polynomially bounded integer weights → (ii) for every connected graph with positive integer weights; reason: (ii) has no constant depending on W
--   - encoding: Δ_ℓ(v) = max over ξ ∈ ℤ≥0 → Nat.findGreatest with search bound 2n; reason: every feasible ξ has e^{ξ/2} ≤ n, so ξ ≤ 2 ln n < 2n and the maximum is the same
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
--   - encoding: undirected graph G = (V, E, w), integral weights in [1, W], connected (standing assumptions, p. 13) → G : WGraph (Fin n) with ℕ weights, HasWeightsIn W (or HasPosWeights), G.adj.Connected; dist in ℕ ∪ {∞}; reason: the standing assumptions of §3 made explicit; distances are integers
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 15, Claim 4.4

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Static

namespace PDynTreeEmbed.Main

/-- **Claim 4.4** (Ball-growth profile [KPGR25], p. 15). (i) For every weight exponent `c_W` there
is `C` such that for every connected graph on `n ≥ 2` vertices with integer weights in `[1, W]`,
`W ≤ n^{c_W}`, and every vertex `v`: `Σ_{ℓ=0}^{L} r_ℓ(v) ≤ C·log₂ n` with `L = ⌈log₂(nW)⌉`.
(ii) For every vertex `v`, every level `ℓ ≥ 1` and every integer `h ≥ 1`:
`|B_G(v, (r_ℓ(v) + h) 2^ℓ)| ≤ e^{h/2} |B_G(v, r_ℓ(v) 2^ℓ)|`. -/
theorem claim_4_4 :
    (∀ cW : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ (n W : ℕ) (G : WGraph (Fin n)), 2 ≤ n →
      (W : ℝ) ≤ (n : ℝ) ^ cW → G.adj.Connected → G.HasWeightsIn W → ∀ v : Fin n,
        ∑ ℓ ∈ Finset.range (levels n W + 1), profile G v ℓ ≤ C * log2 n) ∧
    ∀ (n : ℕ) (G : WGraph (Fin n)), 2 ≤ n → G.adj.Connected → G.HasPosWeights →
      ∀ (v : Fin n) (ℓ : ℕ), 1 ≤ ℓ → ∀ h : ℕ, 1 ≤ h →
        ((G.ball v ((profile G v ℓ + h) * 2 ^ ℓ)).card : ℝ) ≤
          Real.exp ((h : ℝ) / 2) * ((G.ball v (profile G v ℓ * 2 ^ ℓ)).card : ℝ) := by sorry

end PDynTreeEmbed.Main
