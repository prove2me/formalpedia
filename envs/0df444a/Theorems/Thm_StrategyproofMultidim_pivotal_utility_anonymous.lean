-- Prove2me | Theorems.Thm_StrategyproofMultidim_pivotal_utility_anonymous
-- name    : StrategyproofMultidim.pivotal_utility_anonymous
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:17.884246+00:00
-- url     : https://prove2.me/theorems/7f0eedfb-ad28-43f2-a566-f5fdc13e52e3
-- title:
--   Pivotal utility is $m$ second-price auctions; the Pivotal mechanism is anonymous
-- statement:
--   Throughout, $m$ objects are sold to $n$ buyers; buyer $i$ has a valuation vector $v_i=(v_i^k)_k$ with every $v_i^k>0$, a profile $v$ is the $n\times m$ matrix of these vectors, and a mechanism $\mu=(d,p)$ assigns at each profile a decision matrix $d(v)$ ($d_i^k(v)=1$ iff buyer $i$ is sold object $k$) and prices $p_i(v)$; buyer $i$'s utility is $u(\mu_i(v);x)=d_i(v)^{\top}x-p_i(v)$ at true valuation $x$.
--
--   Let $n\ge2$ and let $\mu$ satisfy Definition 7 (efficient decisions with any tie-breaking, Pivotal payments). Then for every positive profile $v$ and buyer $i$,
--   $$u(\mu_i(v);v_i)=\sum_{k\in M,\;d_i^k(v)=1}\Big[v_i^k-\max_{j\neq i}v_j^k\Big],$$
--   so the mechanism runs $m$ separate second-price auctions, and $\mu$ satisfies anonymity in welfare.
--
--   This is the sufficiency half of Theorem 4.
--
--   Differences from the source:
--   - generalization: μᴾ, the Pivotal mechanism under Remark 1's tie-break → any μ with IsPivotal μ (any tie-breaking); reason: the argument does not use the tie-break; it specializes to μᴾ
--   - encoding: max_{j≠i} vⱼᵏ (meaningful for n ≥ 2 only) → 2 ≤ n; maxOthers v i k; reason: excludes the undefined case n = 1
--   - reading: 𝒟: elements of each column sum up to 1 (p.5) → IsFeasible: each column sums to at most 1; reason: p.7 sets 𝒟 = {0,1}ᵐ for one buyer, Theorem 4 assumes selling all objects as a separate hypothesis and §7.2 uses a mechanism that sells nothing; with sums = 1 every mechanism would sell everything. Under the sells-all hypothesis the two readings coincide
--   - generalization: m ≥ 2 and n ≥ 1 (§3, p.5: "Fix any m ≥ 2 and n ≥ 1") → 2 ≤ n (the encoding above) and any m : ℕ; reason: covers the paper's range m ≥ 2; the argument is per object and does not use m ≥ 2
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), proof of Theorem 4 (sufficiency), p.16 (PDF p.17)

import Mathlib
import Definitions.Def_StrategyproofMultidim_IsPivotal
import Definitions.Def_StrategyproofMultidim_AN
import Definitions.Def_StrategyproofMultidim_maxOthers

namespace StrategyproofMultidim

/-- **The Pivotal mechanism is `m` second-price auctions and is anonymous** (p.16).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.16: "Therefore, for all i and all v, u(μᵢᴾ(v); vᵢ) = ∑_{k∈M, dᵢᵏ(v)=1} [vᵢᵏ − max_{j≠i} vⱼᵏ],
that is, the Pivotal mechanism is equivalent to executing m different 'Second Price Auction's -
one for each object to be sold." and "Note that for any bijection π : N ↦ N and any i ∈ N, k ∈ M;
vᵢ = (πv)_{πi}, max_{j≠i} vⱼᵏ = max_{j≠πi} (πv)ⱼᵏ, and so, u(μᵢᴾ(v); vᵢ) = u(μ_{πi}ᴾ(πv); (πv)_{πi}).
Therefore, it is easy to see that μᴾ satisfies anonymity."

Let `n ≥ 2`. For any mechanism satisfying Definition 7 (efficient decisions, any tie-breaking,
Pivotal payments), at every positive profile buyer `i`'s utility is
`∑_{k won by i} (vᵢᵏ − max_{j≠i} vⱼᵏ)`, and the mechanism satisfies AN. -/
theorem pivotal_utility_anonymous {n m : ℕ} (hn : 2 ≤ n) (μ : Mechanism n m) (hP : IsPivotal μ) :
    (∀ v, PosProfile v → ∀ i,
      util μ v i (v i) =
        ∑ k ∈ Finset.univ.filter (fun k => μ.q v i k = true), (v i k - maxOthers v i k)) ∧
    AN μ := by sorry

end StrategyproofMultidim
