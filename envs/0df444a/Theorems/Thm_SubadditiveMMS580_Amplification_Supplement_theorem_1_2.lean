-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_theorem_1_2
-- name    : SubadditiveMMS580.Amplification.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:58:01.492256+00:00
-- url     : https://prove2.me/theorems/3bce6935-fcfb-4175-acd3-b26e8bc1ea34
-- title:
--   Theorem 1.2 — every $n$-agent instance with $q$-partitioning valuations admits a $\rho(q/n)$-MMS allocation
-- statement:
--   Let $q\ge2$ be an integer and let $\rho$ be the function of equation (1):
--   $$\rho(c)=\begin{cases}\dfrac{c}{11-5c},&0<c\le1,\\[4pt] \dfrac16,&1\le c\le\frac65,\\[4pt] \dfrac{2(c-1)}{7c-6},&\frac65\le c\le2,\\[4pt] \dfrac14,&c\ge2.\end{cases}$$
--   Every instance with $n\ge1$ agents whose valuations $v_1,\dots,v_n$ on a finite set $M$ of goods belong to $\mathcal Q_q$ admits a $\rho(q/n)$-MMS allocation: there are pairwise disjoint bundles $A_1,\dots,A_n\subseteq M$ with
--   $$v_i(A_i)\ge\rho(q/n)\cdot\mathrm{MMS}_n(v_i;M)\qquad\text{for every agent }i.$$
--   In particular this gives a $1/6$-MMS allocation when $q\ge n$ and a $1/4$-MMS allocation when $q\ge2n$.
--
--   This companion theorem gives constant MMS guarantees whenever $q/n$ is bounded below, for valuation classes strictly between XOS and subadditive; it is not used in the proof of the mission's goal (Theorem 1.1).
--
--   Differences from the source:
--   - encoding: an n-agent instance → n : ℕ with 1 ≤ n; reason: an instance has at least one agent; c = q/n is then positive
--   - encoding: ρ on the closed pieces of (1), which agree at c = 1, 6/5, 2 → ρ on the half-open pieces (−∞,1], (1,6/5], (6/5,2], (2,∞); reason: adjacent formulas agree at the break points, so the value at every c > 0 is the same
--   - encoding: partitions $(C_1,\dots,C_t)\in\Pi(S,t)$ into $t\le q$ nonempty groups (Definition 2.1) → 1 ≤ t ≤ q and C : Fin t → Finset (Fin m) with nonempty, pairwise disjoint members whose union is S; reason: the same ordered partitions
--   - encoding: valuations $v_i : 2^M \to \mathbb R_{\ge 0}$, normalized and monotone → real set functions on Finset (Fin m) with the published IsNormalized and IsMonotone predicates; reason: normalization and monotonicity give nonnegativity, so the instances are the same
--   - encoding: an allocation (pairwise disjoint bundles, goods may stay unassigned) → IsAllocation A (pairwise disjoint Finset bundles indexed by Fin n); reason: the source allows partial allocations (§2.1, p. 8); completing one cannot lower a monotone value
--   - encoding: $\mathrm{MMS}_n(v_i;M)$, the maximum over ordered partitions of $M$ into $n$ possibly empty bundles of the minimum bundle value → LittleCharity.MMS.mms (v i) n univ, a supremum over labelings Fin m → Fin n of the minimum labelled bundle value; reason: a labeling is exactly an ordered partition into n possibly empty bundles; the index set is finite and nonempty for n ≥ 1, so the supremum is the maximum
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Theorem 1.2, p. 3 (PDF p. 3)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Supplement

/-- Theorem 1.2 (Partitioning valuations; Li–Sun, STOC 2027 submission #580, p. 3): for every
integer `q ≥ 2`, every `n`-agent instance (`n ≥ 1`) with valuations in `Q_q` on the goods
`Fin m` admits a `ρ(q/n)`-MMS allocation, with `ρ` the four-branch function of eq. (1). -/
theorem theorem_1_2 (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 1 ≤ n) {m : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ) (hv : ∀ i, IsQPartitioning q (v i)) :
    ∃ A : Fin n → Finset (Fin m), IsAllocation A ∧
      ∀ i : Fin n, rho ((q : ℝ) / n) * LittleCharity.MMS.mms (v i) n Finset.univ
        ≤ v i (A i) := by sorry

end SubadditiveMMS580.Amplification.Supplement
