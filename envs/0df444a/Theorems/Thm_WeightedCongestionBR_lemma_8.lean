-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_8
-- name    : WeightedCongestionBR.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:19.011227+00:00
-- url     : https://prove2.me/theorems/43645a7d-be05-4207-b6d2-4165d9658512
-- title:
--   Lemma 8 — $\Phi_{R_i}(s^i)\le\alpha\sum_{u\in R_i}C_u(i)$, for any sequence of deviations
-- statement:
--   Let $\Gamma$ be a weighted polynomial congestion game of degree $d\ge1$ with weights $w_u\ge1$. Start from any state $s_0$ and apply any finite sequence of unilateral deviations; let $R$ be the set of players that deviate, $s$ the final state, and $C_u(i)$ the cost of $u\in R$ immediately after its last deviation. Then
--
--   $$
--   \Phi_R(s)\le\alpha\sum_{u\in R}C_u(i).
--   $$
--
--   For the moves of phase $i$ of Algorithm 1 this is the paper's $\Phi_{R_i}(s^i)\le\alpha\sum_{u\in R_i}C_u(i)$.
--
--   Differences from the source:
--   - generalization: the moves of a phase i of Algorithm 1 → any finite list of unilateral deviations from any state; reason: the proof uses only that the moves are unilateral; a phase of Algorithm 1 is such a list, with R_i its movers
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 8, p.15

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_partialPot
import Definitions.Def_WeightedCongestionBR_alphaC
import Definitions.Def_WeightedCongestionBR_runCosts
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- **Lemma 8** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.15), for any finite sequence of unilateral deviations. For every phase `i`,
`Φ_{R_i}(s^i) ≤ α ∑_{u ∈ R_i} C_u(i)`, where `R_i` are the players that moved in phase `i` and `C_u(i)`
is the cost of `u` immediately after its last move in phase `i`.

**Formalization Note** The phase is replaced by an arbitrary list `mv` of unilateral deviations
applied to a state `s₀` (`runCosts`); `R` is the set of players that appear in `mv`, the final
state is `(runCosts G s₀ mv).1` and `C_u(i)` is `(runCosts G s₀ mv).2 u`. A phase of Algorithm 1 is
such a list. Weights satisfy `w_u ≥ 1` (p.6). -/
theorem lemma_8 {n r : ℕ} (G : Game n r) (d : ℕ) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u)
    (s₀ : G.Profile) (mv : List (Σ u : Fin n, G.Strategy u)) :
    partialPot G (mv.map Sigma.fst).toFinset (runCosts G s₀ mv).1 ≤
      alphaC d * ∑ u ∈ (mv.map Sigma.fst).toFinset, (runCosts G s₀ mv).2 u := by sorry

end WeightedCongestionBR
