-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_5
-- name    : WeightedCongestionBR.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:20.217702+00:00
-- url     : https://prove2.me/theorems/404cd631-fe8c-4e63-a9b0-c16d7dca28cd
-- title:
--   Lemma 5 — the partial potential is cost-revealing
-- statement:
--   Let $\Gamma$ be a weighted polynomial congestion game of degree $d\ge1$ with weights $w_u\ge1$. For any group of players $R\subseteq N$ and any state $s$,
--
--   $$
--   \sum_{u\in R}C_u(s)\le\Phi_R(s)\le\alpha\sum_{u\in R}C_u(s).
--   $$
--
--   It converts bounds on the partial potential into bounds on costs, and back, throughout §4.
--
--   Differences from the source:
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 5, p.12

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_groupCost
import Definitions.Def_WeightedCongestionBR_partialPot
import Definitions.Def_WeightedCongestionBR_alphaC
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- **Lemma 5** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.12). For any group of players `R ⊆ N`,
`∑_{u ∈ R} C_u(s) ≤ Φ_R(s) ≤ α ∑_{u ∈ R} C_u(s)`.

**Formalization Note** As in §4 of the paper, weights satisfy `w_u ≥ 1` (p.6); without it Lemma 4,
and this lemma, fail. -/
theorem lemma_5 {n r : ℕ} (G : Game n r) (d : ℕ) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u)
    (R : Finset (Fin n)) (s : G.Profile) :
    groupCost G R s ≤ partialPot G R s ∧ partialPot G R s ≤ alphaC d * groupCost G R s := by sorry

end WeightedCongestionBR
