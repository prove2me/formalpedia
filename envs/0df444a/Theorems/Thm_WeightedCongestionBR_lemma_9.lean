-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_9
-- name    : WeightedCongestionBR.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:06.853647+00:00
-- url     : https://prove2.me/theorems/888d4479-493a-47ca-9531-8c3aa2f2d08a
-- title:
--   Lemma 9 — $\Phi_R(s)\le\alpha\Phi_{d,\rho}^{d+1}\Phi_R(s')$
-- statement:
--   Let $\Gamma$ be a weighted polynomial congestion game of degree $d\ge1$ with weights $w_u\ge1$, and $\rho\ge1$. For any group of players $R\subseteq N$ and any two states $s,s'$ such that $s$ is a $\rho$-equilibrium for the players in $R$ and every player in $N\setminus R$ uses the same strategy in $s$ and $s'$,
--
--   $$
--   \Phi_R(s)\le\alpha\,\Phi_{d,\rho}^{d+1}\,\Phi_R(s').
--   $$
--
--   The Key Property applies it in an auxiliary game with extra resources, which is why it is stated for every game of degree $d$.
--
--   Differences from the source:
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 9, p.16

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_IsGroupEq
import Definitions.Def_WeightedCongestionBR_genGolden
import Definitions.Def_WeightedCongestionBR_partialPot
import Definitions.Def_WeightedCongestionBR_alphaC
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- **Lemma 9** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.16). For any group of players `R ⊆ N` and states `s`, `s'` such that `s` is a
`ρ`-equilibrium for the players in `R` and every player in `N ∖ R` uses the same strategy in `s` and
`s'`: `Φ_R(s) ≤ α Φ_{d,ρ}^{d+1} Φ_R(s')`.

**Formalization Note** Weights satisfy `w_u ≥ 1` (p.6). The game is arbitrary of degree `d`: the
proof of Theorem 3 applies the lemma to a helper game with extra resources. -/
theorem lemma_9 {n r : ℕ} (G : Game n r) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (hG : CongestionApproxPNE.IsPolyGame d G) (hw : ∀ u, 1 ≤ G.demand u)
    (R : Finset (Fin n)) (s s' : G.Profile) (hs : IsGroupEq G ρ R s)
    (hout : ∀ u ∉ R, s u = s' u) :
    partialPot G R s ≤ alphaC d * genGolden d ρ ^ (d + 1) * partialPot G R s' := by sorry

end WeightedCongestionBR
