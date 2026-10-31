-- Prove2me | Theorems.Thm_StrategyproofMultidim_anonymous_iff_efficient
-- name    : StrategyproofMultidim.anonymous_iff_efficient
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:15:41.957463+00:00
-- url     : https://prove2.me/theorems/45435c37-35ba-4986-8e42-c29df8d5b7a2
-- title:
--   Theorem 4 — anonymity iff efficiency
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   Let $\mu$ be a regular mechanism (a buyer who wins nothing pays nothing, and a small change of $v_i^k$ does not change $i$'s decisions on other objects) that is strategyproof and agent sovereign and sells every object at every positive profile. Then
--   $$\mu\ \text{satisfies anonymity in welfare}\iff\mu\ \text{is efficient}.$$
--
--   Together with the Holmström step, the only such anonymous mechanism is the Pivotal mechanism, i.e. $m$ simultaneous second-price auctions.
--
--   Differences from the source:
--   - generalization: μ ∈ Γ̄_{M,N} (continuous, Definition 4) → no continuity hypothesis (μ in Γ_{M,N}); reason: Γ̄ ⊆ Γ, so this specializes to the paper's theorem under any reading of Definition 4; it also removes the dependence on the printed Definition 4, under which Γ̄ is empty
--   - generalization: Remark 1's tie-breaking convention ('henceforth') → no tie-breaking assumption; reason: the statement covers every tie-breaking rule, including Remark 1's
--   - generalization: m ≥ 2 and n ≥ 1 (§3) → any n, m : ℕ; reason: covers the paper's range; for n = 1, m ≥ 1 the hypotheses are inconsistent (selling everything contradicts AS), and m = 0 is trivial
--   - reading: 𝒟: elements of each column sum up to 1 (p.5) → IsFeasible: each column sums to at most 1; reason: p.7 sets 𝒟 = {0,1}ᵐ for one buyer, Theorem 4 assumes selling all objects as a separate hypothesis and §7.2 uses a mechanism that sells nothing; with sums = 1 every mechanism would sell everything. Under the sells-all hypothesis the two readings coincide
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Theorem 4, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_StrategyproofMultidim_IsMechanism
import Definitions.Def_StrategyproofMultidim_IsRegular
import Definitions.Def_StrategyproofMultidim_SP
import Definitions.Def_StrategyproofMultidim_AS
import Definitions.Def_StrategyproofMultidim_AN
import Definitions.Def_StrategyproofMultidim_EFF
import Definitions.Def_StrategyproofMultidim_SellsAll

namespace StrategyproofMultidim

/-- **Theorem 4: anonymity iff efficiency** (p.15).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.15: "Theorem 4. Consider any mechanism μ ∈ Γ̄_{M,N} that sells all objects at all
profiles. Then, μ satisfies AN if and only if it satisfies EFF."

For any numbers of buyers `n` and objects `m`, and any mechanism (feasible decisions,
non-negative prices) that is regular, strategyproof, agent sovereign and sells every object at
every positive profile: the mechanism satisfies anonymity in welfare if and only if it is
efficient.

**Formalization Note.** The continuity hypothesis (`Γ̄ ⊆ Γ`) is not assumed, so this specializes
to the paper's theorem under any reading of Definition 4; the printed Definition 4 makes `Γ̄`
empty. No tie-breaking convention (Remark 1) and no bound on `n`, `m` is assumed. -/
theorem anonymous_iff_efficient {n m : ℕ} (μ : Mechanism n m) (hM : IsMechanism μ) (hR : IsRegular μ) (hSP : SP μ) (hAS : AS μ) (hSell : SellsAll μ) :
    AN μ ↔ EFF μ := by sorry

end StrategyproofMultidim
