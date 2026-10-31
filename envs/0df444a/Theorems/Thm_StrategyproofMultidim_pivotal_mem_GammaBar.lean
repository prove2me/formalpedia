-- Prove2me | Theorems.Thm_StrategyproofMultidim_pivotal_mem_GammaBar
-- name    : StrategyproofMultidim.pivotal_mem_GammaBar
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:32.008988+00:00
-- url     : https://prove2.me/theorems/dbb71ac6-51d8-4a97-98e5-704b7bee45c5
-- title:
--   The Pivotal mechanism is in $\bar\Gamma_{M,N}$ (corrected: $n\ge 2$)
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   Let $n\ge 2$. The Pivotal mechanism $\mu^P$ (each object to the least-index highest bidder, who pays the highest competing bid) is a mechanism with feasible decisions and non-negative prices, is regular, strategyproof, agent sovereign and continuous, sells every object at every profile, satisfies Definition 7 (in particular it is efficient), and satisfies anonymity in welfare.
--
--   So the hypotheses of Theorem 4 are satisfiable and both sides of its equivalence hold for $\mu^P$.
--
--   Differences from the source:
--   - correction: μᴾ ∈ Γ̄_{M,N} for every n ≥ 1 → 2 ≤ n; reason: for n = 1 the Pivotal mechanism gives the buyer every object at price 0, so AS fails
--   - reading: continuity, Definition 4 (same price pᵢ(ṽ) on both sides) → IsContinuous: indifference at the price μ charges for the bundle (ζ, dᵢ⁻ᵏ(ṽ)); reason: the literal definition is unsatisfiable in Γ_{M,N} (it reads ṽᵢᵏ(ζ − dᵢᵏ(ṽ)) = 0) and fails for μᴾ along vˡ = [[1,1],[1+1/l,1]] → [[1,1],[1,1]]; the reading follows the prose of p.12
--   - encoding: convergence in the Frobenius distance (pp.11–12) → convergence in the product topology on Fin n → Fin m → ℝ; reason: the two topologies coincide on a finite-dimensional space
--   - generalization: μᴾ ∈ Γ̄_{M,N} → also SellsAll, IsPivotal (Definition 7, hence EFF) and AN; reason: added conclusions (stated on pp.15–16) that show the hypothesis set of Theorem 4 is inhabited
--   - reading: 𝒟: elements of each column sum up to 1 (p.5) → IsFeasible: each column sums to at most 1; reason: p.7 sets 𝒟 = {0,1}ᵐ for one buyer, Theorem 4 assumes selling all objects as a separate hypothesis and §7.2 uses a mechanism that sells nothing; with sums = 1 every mechanism would sell everything. Under the sells-all hypothesis the two readings coincide
--   - generalization: m ≥ 2 and n ≥ 1 (§3, p.5: "Fix any m ≥ 2 and n ≥ 1") → 2 ≤ n (the correction above) and any m : ℕ; reason: covers the paper's range m ≥ 2; every property is checked object by object
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), proof of Theorem 4, p.16 (PDF p.17); Remark 1, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_StrategyproofMultidim_IsMechanism
import Definitions.Def_StrategyproofMultidim_IsRegular
import Definitions.Def_StrategyproofMultidim_SP
import Definitions.Def_StrategyproofMultidim_AS
import Definitions.Def_StrategyproofMultidim_AN
import Definitions.Def_StrategyproofMultidim_SellsAll
import Definitions.Def_StrategyproofMultidim_IsPivotal
import Definitions.Def_StrategyproofMultidim_pivotal
import Definitions.Def_StrategyproofMultidim_IsContinuous

namespace StrategyproofMultidim

/-- **The Pivotal mechanism belongs to `Γ̄_{M,N}` (corrected: n ≥ 2)** (p.16).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.16: "Thus, μp satisfies continuity. Finally, it is easy to see that Pivotal mechanism
satisfies strategyproofness and agent sovereignty. Thus, μᴾ ∈ Γ̄_{M,N}."

Let `n ≥ 2`. The Pivotal mechanism with the tie-break of Remark 1 (`pivotal n m`: each object to
the least-index highest bidder, who pays the highest competing bid) is a mechanism (feasible,
non-negative prices), regular, strategyproof, agent sovereign, continuous (in the reading of
`IsContinuous`), sells every object at every profile, is the Pivotal mechanism of Definition 7
(in particular efficient), and satisfies AN.

**Formalization Note.** For `n = 1` agent sovereignty fails (the buyer gets everything at price
0), hence `2 ≤ n`. -/
theorem pivotal_mem_GammaBar {n m : ℕ} (hn : 2 ≤ n) :
    IsMechanism (pivotal n m) ∧ IsRegular (pivotal n m) ∧ SP (pivotal n m) ∧
      AS (pivotal n m) ∧ IsContinuous (pivotal n m) ∧ SellsAll (pivotal n m) ∧
      IsPivotal (pivotal n m) ∧ AN (pivotal n m) := by sorry

end StrategyproofMultidim
