-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_proposition_4_3
-- name    : SubadditiveMMS580.Amplification.Supplement.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:56:26.534735+00:00
-- url     : https://prove2.me/theorems/5ea9cbd2-a9f9-494b-a508-8e75cd0f18d3
-- title:
--   Proposition 4.3 — $\mathcal Q_q$ instances admit $1/(11\max\{1,n/q\}-5)$-MMS allocations
-- statement:
--   Let $n,q\ge2$ be integers, $x=\max\{1,n/q\}$ and $\alpha=1/(11x-5)$. Every instance with $n$ agents and valuations $v_1,\dots,v_n\in\mathcal Q_q$ on a finite set $M$ of goods admits an $\alpha$-MMS allocation: there are pairwise disjoint bundles $A_1,\dots,A_n\subseteq M$ with
--   $$v_i(A_i)\ge\frac{1}{11\max\{1,n/q\}-5}\cdot\mathrm{MMS}_n(v_i;M)\qquad\text{for every agent }i.$$
--   Here $\mathrm{MMS}_n(v;M)$ is the maximum, over ordered partitions of $M$ into $n$ possibly empty bundles, of the minimum bundle value.
--
--   It gives the first two branches of $\rho$ in Theorem 1.2 ($q/(11n-5q)$ for $q\le n$ and $1/6$ for $q\ge n$).
--
--   Differences from the source:
--   - reading: 'Algorithm 2 returns an α-MMS allocation on the working instance. Consequently, every instance with valuations in Q_q admits an α-MMS allocation' → the existence of an α-MMS allocation for every instance with valuations in Q_q; reason: the working instance is one such instance, so its claim is a special case of the stated conclusion; Algorithm 2 is the procedure of the proof, not a separate mathematical object
--   - encoding: partitions $(C_1,\dots,C_t)\in\Pi(S,t)$ into $t\le q$ nonempty groups (Definition 2.1) → 1 ≤ t ≤ q and C : Fin t → Finset (Fin m) with nonempty, pairwise disjoint members whose union is S; reason: the same ordered partitions
--   - encoding: valuations $v_i : 2^M \to \mathbb R_{\ge 0}$, normalized and monotone → real set functions on Finset (Fin m) with the published IsNormalized and IsMonotone predicates; reason: normalization and monotonicity give nonnegativity, so the instances are the same
--   - encoding: an allocation (pairwise disjoint bundles, goods may stay unassigned) → IsAllocation A (pairwise disjoint Finset bundles indexed by Fin n); reason: the source allows partial allocations (§2.1, p. 8); completing one cannot lower a monotone value
--   - encoding: $\mathrm{MMS}_n(v_i;M)$, the maximum over ordered partitions of $M$ into $n$ possibly empty bundles of the minimum bundle value → LittleCharity.MMS.mms (v i) n univ, a supremum over labelings Fin m → Fin n of the minimum labelled bundle value; reason: a labeling is exactly an ordered partition into n possibly empty bundles; the index set is finite and nonempty for n ≥ 1, so the supremum is the maximum
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Proposition 4.3, p. 22 (PDF p. 22)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Supplement

/-- Proposition 4.3 (Li–Sun, STOC 2027 submission #580, p. 22): for integers `n, q ≥ 2`, with
`x = max {1, n/q}` and `α = 1/(11x − 5)`, every instance with `n` agents and valuations in
`Q_q` on the goods `Fin m` admits an `α`-MMS allocation: pairwise disjoint bundles `A_i` with
`v_i(A_i) ≥ α · MMS_n(v_i; M)`. -/
theorem proposition_4_3 (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) {m : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ) (hv : ∀ i, IsQPartitioning q (v i)) :
    ∃ A : Fin n → Finset (Fin m), IsAllocation A ∧
      ∀ i : Fin n, 1 / (11 * max 1 ((n : ℝ) / q) - 5) * LittleCharity.MMS.mms (v i) n Finset.univ
        ≤ v i (A i) := by sorry

end SubadditiveMMS580.Amplification.Supplement
