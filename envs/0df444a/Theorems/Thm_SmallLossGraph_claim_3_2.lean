-- Prove2me | Theorems.Thm_SmallLossGraph_claim_3_2
-- name    : SmallLossGraph.claim_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:24.47199+00:00
-- url     : https://prove2.me/theorems/e1b42d97-2450-42cb-8ca4-ac841b41389b
-- title:
--   Claim 3.2 — the initially frozen mass is at most $\alpha(G)\gamma$
-- statement:
--   Let $G$ be a graph on the arms whose independent sets have at most $\alpha$ vertices, let $p$ be a nonnegative vector on the arms and $\gamma>0$. The initial freezing step of Algorithm 1 freezes $F_0=\{i:\sum_{j\in N_i}p_j<\gamma\}$, where $N_i$ is the closed neighbourhood of $i$. Then
--
--   $$
--   \sum_{i\in F_0}p_i\le\alpha\,\gamma .
--   $$
--
--   This is the first half of the bound on the frozen mass (Lemma 3.1): the mass removed by the first threshold scales with the independence number of the feedback graph, not with the number of arms.
--
--   Differences from the source:
--   - encoding: α(G^t), the independence number → any α bounding the independent sets of G; reason: equivalent: α = α(G) is such a bound, and the printed bound with α(G) ≤ α gives the bound with α since γ > 0
--   - generalization: γ = ε′/(4α) of Algorithm 1 → every γ > 0; reason: F_0 and the claim depend on γ only; the algorithm's γ is one value
--   - generalization: p^t, A's probability vector → any nonnegative vector p; reason: the claim uses only p ≥ 0; probability vectors are nonnegative
--   - encoding: round t of Algorithm 1 (p^t, G^t, ℓ^t) → one round with the superscript t dropped; reason: the statement concerns a single round
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, Claim 3.2, p.9

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing

open scoped BigOperators

namespace SmallLossGraph

/-- **Claim 3.2 (initial frozen mass).**
Lykouris–Sridharan–Tardos, arXiv:1711.03639v5, Claim 3.2, p.9: "The total probability frozen in
the initial step is bounded by `∑_{i∈F^t_0} p^t_i ≤ α(G^t)γ`."

For every graph `G` on the arms, every `α` bounding the independent sets of `G`, every
nonnegative vector `p` and every threshold `γ > 0`, `∑_{i ∈ F_0} p_i ≤ α γ`, where
`F_0 = {i : ∑_{j ∈ N_i} p_j < γ}`.

**Formalization Note** One round (the index `t` is dropped). Taking `α = α(G)` gives the printed
claim, and the printed claim gives the bound for every `α ≥ α(G)`. The claim is stated for every
`γ > 0` (the algorithm's `γ = ε′/(4α)` is one value). -/
theorem claim_3_2 {d : ℕ} (G : SimpleGraph (Fin d)) (α : ℕ) (hα : IndepBound G α)
    (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (γ : ℝ) (hγ : 0 < γ) :
    ∑ i ∈ frozen0 G p γ, p i ≤ (α : ℝ) * γ := by sorry

end SmallLossGraph
