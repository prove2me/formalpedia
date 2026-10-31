-- Prove2me | Theorems.Thm_StrategyproofMultidim_efficient_isPivotal
-- name    : StrategyproofMultidim.efficient_isPivotal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:24.75085+00:00
-- url     : https://prove2.me/theorems/8dcdcc3d-edc8-4a08-9c2a-f2e0f13a4e91
-- title:
--   Holmström step — an efficient mechanism in $\Gamma_{M,N}$ is the Pivotal mechanism
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   Let $\mu$ be a regular, strategyproof, agent-sovereign mechanism that is efficient (Definition 6). Then $\mu$ satisfies Definition 7: at every positive profile $v$, every buyer $i$ pays
--   $$p_i(v)=\max_{\hat d\in\mathcal D}\sum_{t\neq i}\hat d_t^{\top}v_t-\sum_{t\neq i}d_t(v)^{\top}v_t .$$
--
--   This is the instance of Holmström's characterization of efficient strategyproof mechanisms that the proof of Theorem 4 uses; regularity (i), "bidders pay no price if they do not win any object", fixes the free constant of the Groves payments.
--
--   Differences from the source:
--   - reading: any efficient mechanism in Γ_{M,N} must be the following Pivotal mechanism → IsPivotal μ: efficient decisions and Definition 7's payments, with whatever tie-breaking μ uses; reason: efficient decisions are not unique at ties, so 'must be the Pivotal mechanism' means 'satisfies Definition 7'
--   - reading: 𝒟: elements of each column sum up to 1 (p.5) → IsFeasible: each column sums to at most 1; reason: p.7 sets 𝒟 = {0,1}ᵐ for one buyer, Theorem 4 assumes selling all objects as a separate hypothesis and §7.2 uses a mechanism that sells nothing; with sums = 1 every mechanism would sell everything. Under the sells-all hypothesis the two readings coincide
--   - generalization: m ≥ 2 and n ≥ 1 (§3, p.5: "Fix any m ≥ 2 and n ≥ 1") → any n, m : ℕ; reason: covers the paper's range; for n = 1, m ≥ 1 the hypotheses are inconsistent (EFF sells everything to the one buyer, contradicting AS), and m = 0 gives price 0 by regularity (i)
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), proof of Theorem 4 (sufficiency), p.15 (PDF p.16), and Definition 7

import Mathlib
import Definitions.Def_StrategyproofMultidim_IsMechanism
import Definitions.Def_StrategyproofMultidim_IsRegular
import Definitions.Def_StrategyproofMultidim_SP
import Definitions.Def_StrategyproofMultidim_AS
import Definitions.Def_StrategyproofMultidim_IsPivotal

namespace StrategyproofMultidim

/-- **Holmström step: an efficient mechanism in `Γ_{M,N}` is the Pivotal mechanism** (p.15).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.15: "Since bidders pay no price if they do not win any object, by the famous
characterization result of Holmström [13], any efficient mechanism in Γ_{M,N} must be the
following Pivotal mechanism."

A regular, strategyproof, agent-sovereign mechanism that is efficient (Definition 6) charges the
Pivotal payments of Definition 7: buyer `i` pays the maximal value the other buyers could obtain
minus the value they obtain at the chosen decision. -/
theorem efficient_isPivotal {n m : ℕ} (μ : Mechanism n m) (hM : IsMechanism μ) (hR : IsRegular μ) (hSP : SP μ) (hAS : AS μ) (hE : EFF μ) :
    IsPivotal μ := by sorry

end StrategyproofMultidim
