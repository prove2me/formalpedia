-- Prove2me | Theorems.Thm_SmallLossGraph_claim_3_3
-- name    : SmallLossGraph.claim_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:44.001056+00:00
-- url     : https://prove2.me/theorems/399fc8ab-7fe4-439a-aec0-9fa6d56ffd98
-- title:
--   Claim 3.3 — propagation freezes at most three times the initially frozen mass
-- statement:
--   Let $G$ be a graph on the arms, $p$ a nonnegative vector on the arms, $\gamma>0$ and $\gamma'=\gamma/3$. Let $F_0,F_1,F_2,\dots$ be the freezing steps of Algorithm 1: $F_0=\{i:\sum_{j\in N_i}p_j<\gamma\}$ and, for $k\ge1$, $F_k=\{i\notin\bigcup_{m<k}F_m:\sum_{j\in N_i\setminus\bigcup_{m<k}F_m}p_j<\gamma'\}$. Then
--
--   $$
--   \sum_{i\in\bigcup_{k\ge1}F_k}p_i\le3\sum_{i\in F_0}p_i .
--   $$
--
--   Together with Claim 3.2 this bounds the whole frozen mass by $4\alpha\gamma=\varepsilon'$ (Lemma 3.1): the cascade caused by the lower threshold $\gamma'$ cannot amplify the initial freezing by more than a factor of three.
--
--   Differences from the source:
--   - generalization: γ = ε′/(4α), γ′ = γ/3 of Algorithm 1 → every γ > 0 with γ′ = γ/3; reason: the freezing steps depend on γ and γ′ only; the algorithm's γ is one value
--   - generalization: p^t, A's probability vector → any nonnegative vector p; reason: the claim uses only p ≥ 0; probability vectors are nonnegative
--   - encoding: round t of Algorithm 1 (p^t, G^t, ℓ^t) → one round with the superscript t dropped; reason: the statement concerns a single round
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, Claim 3.3, p.9 (proof pp.9–10)

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing

open scoped BigOperators

namespace SmallLossGraph

/-- **Claim 3.3 (propagation freezes at most three times the initial mass).**
Lykouris–Sridharan–Tardos, arXiv:1711.03639v5, Claim 3.3, p.9: "The total probability frozen in
the propagation steps is bounded by three times the total probability frozen at the initial
step. More formally: `∑_{i∈⋃_{k≥1} F^t_k} p^t_i ≤ 3 ∑_{i∈F^t_0} p^t_i`."

For every graph `G`, every nonnegative vector `p` and every `γ > 0`, with `γ′ = γ/3` and the
freezing steps `F_0, F_1, …` of Algorithm 1 (lines 3–4),
`∑_{i ∈ ⋃_{k≥1} F_k} p_i ≤ 3 ∑_{i ∈ F_0} p_i`.

**Formalization Note** One round (the index `t` is dropped). The claim is stated for every
`γ > 0` with `γ′ = γ/3` (the algorithm's `γ = ε′/(4α)` is one value); no bound on independent
sets is needed. -/
theorem claim_3_3 {d : ℕ} (G : SimpleGraph (Fin d)) (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i)
    (γ : ℝ) (hγ : 0 < γ) :
    ∑ i ∈ propFrozen G p γ (γ / 3), p i ≤ 3 * ∑ i ∈ frozen0 G p γ, p i := by sorry

end SmallLossGraph
