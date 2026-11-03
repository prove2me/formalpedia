-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_6
-- name    : WeightedCongestionBR.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:08.145617+00:00
-- url     : https://prove2.me/theorems/264a0505-550e-4fd4-b41a-69845194dadf
-- title:
--   Lemma 6 — potential change under one deviation
-- statement:
--   Let $\Gamma$ be a weighted polynomial congestion game of degree $d\ge1$ with weights $w_u\ge1$. Let $u$ be a player, $R$ a set of players with $u\in R$, and $s,s'$ two states that differ only in the strategy of player $u$. Then
--
--   $$
--   \Phi_R(s)-\Phi_R(s')\ge C_u(s)-\alpha\,C_u(s').
--   $$
--
--   So a move that improves the mover's cost by more than a factor $\alpha$ decreases the partial potential of every group containing the mover.
--
--   Differences from the source:
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 6, p.12

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_partialPot
import Definitions.Def_WeightedCongestionBR_alphaC
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- **Lemma 6** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.12). Let `u` be a player, `R` a set of players with `u ∈ R`, and `s`, `s'`
states that differ only in the strategy of `u`. Then `Φ_R(s) − Φ_R(s') ≥ C_u(s) − α C_u(s')`.

**Formalization Note** Weights satisfy `w_u ≥ 1` (p.6). -/
theorem lemma_6 {n r : ℕ} (G : Game n r) (d : ℕ) (hd : 1 ≤ d)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u)
    (u : Fin n) (R : Finset (Fin n)) (hu : u ∈ R) (s s' : G.Profile) (hss' : ∀ v, v ≠ u → s v = s' v) :
    privateCost G s u - alphaC d * privateCost G s' u ≤ partialPot G R s - partialPot G R s' := by sorry

end WeightedCongestionBR
