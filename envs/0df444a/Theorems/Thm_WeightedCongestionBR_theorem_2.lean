-- Prove2me | Theorems.Thm_WeightedCongestionBR_theorem_2
-- name    : WeightedCongestionBR.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:43.398379+00:00
-- url     : https://prove2.me/theorems/fa953fbd-bad2-4abc-a334-42a6b69ddda1
-- title:
--   Theorem 2 — singleton games with $\rho$-PoA at least $\Phi_{d,\rho}^{d+1}-\varepsilon$
-- statement:
--   Let $d$ be a positive integer and $\rho\ge1$. For every $\varepsilon>0$ there is a singleton weighted polynomial congestion game of degree $d$ (every strategy consists of exactly one resource) whose $\rho$-approximate Price of Anarchy is at least $\Phi_{d,\rho}^{d+1}-\varepsilon$: it has a $\rho$-equilibrium $s$ and a minimizer $s^*$ of the social cost with $C(s^*)>0$ and
--
--   $$
--   \frac{C(s)}{C(s^*)}\ge\Phi_{d,\rho}^{d+1}-\varepsilon .
--   $$
--
--   It shows that Theorem 1 is tight, so $\mathrm{PoA}_d(\rho)=\Phi_{d,\rho}^{d+1}$.
--
--   Differences from the source:
--   - encoding: the game's ρ-approximate PoA is at least Φ^{d+1} − ε → a ρ-equilibrium s and a social-cost minimizer s* with C(s*) > 0 and C(s)/C(s*) ≥ Φ^{d+1} − ε; reason: the PoA of a game is the maximum of these ratios over its ρ-equilibria
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 2, p.9

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_WeightedCongestionBR_groupCost
import Definitions.Def_WeightedCongestionBR_IsGroupEq
import Definitions.Def_WeightedCongestionBR_genGolden
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- **Theorem 2** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.9). Let `d` be a positive integer and `ρ ≥ 1`. For every `ε > 0` there is a
singleton weighted polynomial congestion game of degree `d` whose `ρ`-approximate PoA is at least
`Φ_{d,ρ}^{d+1} − ε`.

**Formalization Note** "Singleton" (footnote 11): every strategy has exactly one resource. "PoA at
least `B − ε`" is stated by a `ρ`-equilibrium `s` and a social-cost minimizer `s*` with `C(s*) > 0` and
`C(s)/C(s*) ≥ B − ε`. -/
theorem theorem_2 (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n r : ℕ) (G : Game n r), CongestionApproxPNE.IsPolyGame d G ∧
      (∀ u : Fin n, ∀ t ∈ G.strategies u, t.card = 1) ∧
      ∃ s sStar : G.Profile, IsGroupEq G ρ Finset.univ s ∧
        (∀ s' : G.Profile, groupCost G Finset.univ sStar ≤ groupCost G Finset.univ s') ∧
        0 < groupCost G Finset.univ sStar ∧
        genGolden d ρ ^ (d + 1) - ε ≤ groupCost G Finset.univ s / groupCost G Finset.univ sStar := by sorry

end WeightedCongestionBR
