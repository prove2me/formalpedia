-- Prove2me | Theorems.Thm_ValTrackRM_Public_Supplement_theorem_3
-- name    : ValTrackRM.Public.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:00:13.977804+00:00
-- url     : https://prove2.me/theorems/4d0fd2a2-2898-463f-9b5a-10443e1d53e7
-- title:
--   Theorem 3 — strict rejection monotonicity (corrected: source typo)
-- statement:
--   Fix a deterministic valuation prefix $W$, a positive inventory $k$, a nonempty strictly increasing positive price grid, and any fixed minimum-level selector. Let $i$ be the next selected unit and $S_i$ its Algorithm 1 sold indicator. Suppose $0<\Pr[S_i=1]<1$. For any two remaining inventory states $a<b$ with positive mass,
--   $$\Pr[S_i=1\mid I=a]>\Pr[S_i=1\mid I=b].$$
--   Thus the corrected Algorithm 1 prime rejection probability strictly decreases as remaining inventory increases. The domain includes every reachable pair, even when some other units have deterministic sold indicators.
--
--   **Formalization Note** The inventory is the number of unsold units, $I=\sum_i(1-S_i)$, as in Definition 2. The ec7 proof's extra leading $k-$ is a typographical error. No additional nondegeneracy assumption is imposed on other units.
--
--   Differences from the source:
--
--   - correction: the ec7 proof prints I=k-sum(1-S_i) → the inventory is sum(1-S_i)=k-sum S_i; reason: Definition 2 and the same proof equation EC.7 determine the correct complement, without excluding any case
--   - generalization: Algorithm 1 leaves arg-min ties unspecified → every fixed minimum-level selector is allowed; reason: the assignment must be deterministic for a fixed valuation prefix; no special tie-break is used
--   - encoding: prices r^(1),...,r^(m),infinity and valuation values → price codes 0,...,m, with m meaning rejection, and valuation indices 0,...,m; reason: this is a bijection on the strictly increasing positive price grid; rejection has zero revenue
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 16, Theorem 3

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Inventory

namespace ValTrackRM.Public.Supplement

theorem theorem_3
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (W : List (Fin (m + 1)))
    (hpos : 0 < probSold r sel W (sel (levels sel W)))
    (hlt : probSold r sel W (sel (levels sel W)) < 1)
    (a b : Fin (k + 1)) (hab : a.val < b.val)
    (ha : 0 < a1Stock r sel W a.val) (hb : 0 < a1Stock r sel W b.val) :
    soldConditional r sel W b.val < soldConditional r sel W a.val := by sorry

end ValTrackRM.Public.Supplement
