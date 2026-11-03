-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_1
-- name    : WeightedCongestionBR.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:50.721183+00:00
-- url     : https://prove2.me/theorems/f6254c8f-b43d-489a-8da0-d76d9eec5b3a
-- title:
--   Lemma 1 — group social cost ratio at most $\Phi_{d,\rho}^{d+1}$
-- statement:
--   Let $\Gamma$ be a weighted polynomial congestion game of degree $d\ge1$ and $\rho\ge1$. For any group of players $R\subseteq N$, let $s$ and $s^*$ be states such that $s$ is a $\rho$-equilibrium for $R$ and every player in $N\setminus R$ uses the same strategy in $s$ and $s^*$. Then
--
--   $$
--   \frac{C_R(s)}{C_R(s^*)}\le\Phi_{d,\rho}^{d+1}, \qquad\text{stated as}\qquad C_R(s)\le\Phi_{d,\rho}^{d+1}\,C_R(s^*).
--   $$
--
--   With $R=N$ it gives the upper bound of Theorem 1; for groups it is used through Lemma 9 in the proof of the Key Property (Theorem 3).
--
--   Differences from the source:
--   - generalization: ratio C_R(s)/C_R(s*) ≤ Φ^{d+1} → C_R(s) ≤ Φ^{d+1} C_R(s*); reason: equivalent to the ratio when C_R(s*) > 0; it also covers C_R(s*) = 0, where the ratio is undefined
--   - encoding: finite player and resource sets N, E → Fin n, Fin r with n, r ≥ 1 (HarksKlimm.Consistency.Game); reason: excludes only games without players or resources, where every cost is 0 and the statement is empty
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 1, p.7

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

/-- **Lemma 1** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.7). For any group of players `R ⊆ N`, if `s` is a `ρ`-equilibrium for `R`
and every player of `N ∖ R` uses the same strategy in `s` and `s*`, then
`C_R(s)/C_R(s*) ≤ Φ_{d,ρ}^{d+1}`.

**Formalization Note** Stated multiplicatively, `C_R(s) ≤ Φ_{d,ρ}^{d+1} C_R(s*)`, which is the
ratio bound when `C_R(s*) > 0` and also covers `C_R(s*) = 0`. Weights are only assumed positive. -/
theorem lemma_1 {n r : ℕ} (G : Game n r) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (hG : CongestionApproxPNE.IsPolyGame d G) (R : Finset (Fin n)) (s sStar : G.Profile)
    (hs : IsGroupEq G ρ R s) (hout : ∀ u ∉ R, s u = sStar u) :
    groupCost G R s ≤ genGolden d ρ ^ (d + 1) * groupCost G R sStar := by sorry

end WeightedCongestionBR
