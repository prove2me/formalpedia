-- Prove2me | Theorems.Thm_StrategyproofMultidim_utility_nonneg
-- name    : StrategyproofMultidim.utility_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:40.917693+00:00
-- url     : https://prove2.me/theorems/cb3c6474-edd4-42b0-b591-bcd789f274b8
-- title:
--   Footnote 22 — truthful utility in a strategyproof mechanism is non-negative
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   Let $\mu$ be a regular, strategyproof and agent-sovereign mechanism. At every positive profile $v$, every buyer $i$ obtains non-negative utility from truthful reporting, $u(\mu_i(v);v_i)\ge 0$. Moreover, for every threshold representation $T$ of $\mu$ (Theorem 2),
--   $$u(\mu_i(v);v_i)=\sum_{k\in M}\max\{0,\;v_i^k-T_i^k(v_{-i})\}.$$
--
--   The identity says each buyer collects, object by object, the surplus of its value over its threshold.
--
--   Differences from the source:
--   - reading: any strategyproof mechanism ("By Theorem 2") → a regular mechanism with SP and AS (μ ∈ Γ_{M,N}); reason: the footnote invokes Theorem 2, which is about Γ_{M,N}; without AS an SP mechanism can give negative utility (always sell object 1 to buyer 1 at price 100)
--   - generalization: utility is non-negative → non-negative, and equal to Σₖ max(0, vᵢᵏ − Tᵢᵏ(v₋ᵢ)) for every threshold representation T; reason: an added conclusion; the first conjunct is the footnote
--   - reading: 𝒟: elements of each column sum up to 1 (p.5) → IsFeasible: each column sums to at most 1; reason: p.7 sets 𝒟 = {0,1}ᵐ for one buyer, Theorem 4 assumes selling all objects as a separate hypothesis and §7.2 uses a mechanism that sells nothing; with sums = 1 every mechanism would sell everything. Under the sells-all hypothesis the two readings coincide
--   - generalization: m ≥ 2 and n ≥ 1 (§3, p.5: "Fix any m ≥ 2 and n ≥ 1") → any n, m : ℕ; reason: covers the paper's range; the identity holds for every n and m
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), footnote 22, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_StrategyproofMultidim_IsMechanism
import Definitions.Def_StrategyproofMultidim_IsRegular
import Definitions.Def_StrategyproofMultidim_SP
import Definitions.Def_StrategyproofMultidim_AS
import Definitions.Def_StrategyproofMultidim_IsThresholdRep
import Definitions.Def_StrategyproofMultidim_util

namespace StrategyproofMultidim

/-- **Footnote 22: utility in a strategyproof mechanism is non-negative** (p.22).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.22, footnote 22: "By Theorem 2, utility from any strategyproof mechanism is
non-negative."

For a mechanism in `Γ_{M,N}` (regular, SP, AS), truthful reporting gives every buyer
non-negative utility at every positive profile; moreover, for every threshold representation `T`,
that utility equals `∑ₖ max(0, vᵢᵏ − Tᵢᵏ(v₋ᵢ))`. -/
theorem utility_nonneg {n m : ℕ} (μ : Mechanism n m) (hM : IsMechanism μ) (hR : IsRegular μ) (hSP : SP μ) (hAS : AS μ)
    (v : Fin n → Fin m → ℝ) (hv : PosProfile v) (i : Fin n) :
    0 ≤ util μ v i (v i) ∧
      ∀ T, IsThresholdRep μ T → util μ v i (v i) = ∑ k, max 0 (v i k - T i k v) := by sorry

end StrategyproofMultidim
