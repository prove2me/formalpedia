-- Prove2me | Theorems.Thm_PLCMarkets_Rationality_isEquilibrium_iff_maxFlow
-- name    : PLCMarkets.Rationality.isEquilibrium_iff_maxFlow
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:59:31.193248+00:00
-- url     : https://prove2.me/theorems/3d9ff596-ef8e-49d6-8b9d-b6dc242a7244
-- title:
--   LEMMA 3.1 — p are equilibrium prices iff max-flow in N(p) is Σ unspent(i)
-- statement:
--   Let $M$ be a Fisher market with additively separable piecewise-linear concave utilities, and let $p$ be prices with
--
--   1. $p_j>0$ for every good $j$;
--   2. $\sum_jp_j=\sum_ie(i)$ (the prices sum to the buyers' total money);
--   3. $\mathrm{unspent}(i)\ge0$ for every buyer $i$ and $\mathrm{unsold}(j)\ge0$ for every good $j$.
--
--   Then $p$ are equilibrium prices if and only if the max-flow value of the network $N(p)$ is
--   $$\sum_{i\in B}\mathrm{unspent}(i).$$
--
--   This reduces checking an equilibrium to one max-flow computation and is the criterion by which the proof of Theorem 4.1 recognises the rational optimal solution of its LP as equilibrium prices.
--
--   **Formalization Note.** Hypotheses 1–3 are the standing assumptions of Section 3 of the paper: nonzero prices (§3.1), the display $\sum_jp_j=\sum_ie(i)$ (§3), and the first sentence of §3.2, which rejects prices violating 3 before the network is built. The index $k_i$ of §3.1 always exists at positive prices, because the last, unbounded segment of every $f^i_j$ has infinite value. See `EquilibriumNetwork` for the network and its max-flow.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, https://doi.org/10.1145/1970392.1970394, p. 10:8, LEMMA 3.1 (standing assumptions: §3 display p. 10:7, §3.1 first sentence p. 10:7, §3.2 first sentence p. 10:8)

import Mathlib
import Definitions.Def_PLCMarkets_Rationality_EquilibriumNetwork

namespace PLCMarkets.Rationality

/-- **LEMMA 3.1** (Vazirani–Yannakakis 2011, §3.2, p. 10:8). Under the standing assumptions of
Section 3 — positive prices (§3.1, "Given nonzero prices"), `Σ_j p_j = Σ_i e(i)` (§3), and
`unspent(i) ≥ 0`, `unsold(j) ≥ 0` (§3.2, first sentence) — the prices `p` are equilibrium prices
iff the max-flow value of the network `N(p)` equals `Σ_i unspent(i)`. (With positive prices, `k_i`
exists for every buyer, since the unbounded last segment of every `f^i_j` has infinite value.) -/
theorem isEquilibrium_iff_maxFlow {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ)
    (hp : ∀ j, 0 < p j)
    (hsum : ∑ j, p j = ∑ i, (M.budget i : ℝ))
    (hunspent : ∀ i, 0 ≤ M.unspent p i)
    (hunsold : ∀ j, 0 ≤ M.unsold p j) :
    M.IsEquilibrium p ↔ M.maxFlow p = ∑ i, M.unspent p i := by sorry

end PLCMarkets.Rationality
