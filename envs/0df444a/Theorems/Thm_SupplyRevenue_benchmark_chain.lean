-- Prove2me | Theorems.Thm_SupplyRevenue_benchmark_chain
-- name    : SupplyRevenue.benchmark_chain
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:50.432251+00:00
-- url     : https://prove2.me/theorems/f1e02145-c5fd-4b7a-ae86-1f8c1d15136b
-- title:
--   Benchmark chain — OblivItemRev ≤ FixedItemRev ≤ SeqItemRev ≤ $A_1$ ≤ $B$
-- statement:
--   Let $D$ be an independent finite instance on $n,m\ge 1$. For every order $\pi$,
--
--   $$\mathrm{OblivItemRev}(D)\le\mathrm{FixedItemRev}(D,\pi)\le\mathrm{SeqItemRev}(D,\pi)\le A_1(D)\le B(D).$$
--
--   Moreover randomization cannot improve one known-order supremum: finite mixtures of matrices in the order $\pi$ have the same supremum as single matrices, and finite mixtures of adaptive policies the same supremum as single policies.
--
--   The chain is what turns the lower bounds against sequential policies into bounds against $\mathrm{OblivItemRev}$.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: "SeqItemRev adapts to sales" → finite mixtures of deterministic policies mapping the list of earlier purchases to an offer; reason: R8: behavioural coins over finitely many histories are such a mixture (Kuhn)
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §1.1, p.2

import Mathlib
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_BuyMany
import Definitions.Def_SupplyRevenue_Revenue

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§1.1, p.2: "For every π, OblivItemRev ≤ FixedItemRev(D, π) ≤ SeqItemRev(D, π) ≤ A1 ≤ B; randomization cannot improve one
known-order supremum."

**Formalization Note** Any finite monotone instance and any residual order. The last two clauses are "randomization
cannot improve": mixtures of matrices do not beat one matrix in a known order, and mixtures of policies do not beat one
policy. Suprema are in `ℝ≥0∞`. -/
theorem benchmark_chain {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (tie : Tie m) (D : Instance n m)
    (π : Equiv.Perm (Fin n)) :
    oblivRev tie D ≤ fixedRev tie D π ∧
    fixedRev tie D π ≤ seqRev tie D π ∧
    seqRev tie D π ≤ capRev tie D 1 ∧
    capRev tie D 1 ≤ buyManyRev D ∧
    fixedRev tie D π = (⨆ mixture : Mix (Matrix' n m),
      ENNReal.ofReal (mixture.E fun P => rev tie D P π)) ∧
    seqRev tie D π = ⨆ pol : Policy m, ENNReal.ofReal (policyRev tie D pol π) := by sorry

end SupplyRevenue
