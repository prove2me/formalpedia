-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_theorem_1_3
-- name    : SubadditiveMMS580.Amplification.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:01:50.399202+00:00
-- url     : https://prove2.me/theorems/3b8b5428-2fe9-4dfc-8f0f-e2dba772bb96
-- title:
--   Theorem 1.3 — every instance with XOS valuations admits a $5/16$-MMS allocation
-- statement:
--   Let $n\ge1$ agents have **XOS** valuations $v_1,\dots,v_n$ on a finite set $M$ of goods: each $v_i$ is the maximum of finitely many (at least one) additive valuations with nonnegative coefficients, $v_i(S)=\max_\ell\sum_{g\in S}w_\ell(g)$. Then there are pairwise disjoint bundles $A_1,\dots,A_n\subseteq M$ with
--   $$v_i(A_i)\ge\frac{5}{16}\,\mathrm{MMS}_n(v_i;M)\qquad\text{for every agent }i,$$
--   where $\mathrm{MMS}_n(v;M)$ is the maximum, over ordered partitions of $M$ into $n$ possibly empty bundles, of the minimum bundle value.
--
--   This companion theorem improves the universal MMS guarantee for XOS valuations from $4/17$ to $5/16$; it is not used in the proof of the mission's goal (Theorem 1.1).
--
--   Differences from the source:
--   - encoding: XOS: the maximum of finitely many additive valuations → DSICHardRev.IsXOS: a nonempty finite family of nonnegative weight vectors with v(S) = max_ℓ w_ℓ(S); reason: additive valuations have nonnegative coefficients (§2.2, p. 9), and a maximum of finitely many requires at least one
--   - encoding: every instance → n : ℕ agents with 1 ≤ n, any m; reason: an instance has at least one agent
--   - encoding: an allocation (pairwise disjoint bundles, goods may stay unassigned) → IsAllocation A (pairwise disjoint Finset bundles indexed by Fin n); reason: the source allows partial allocations (§2.1, p. 8); completing one cannot lower a monotone value
--   - encoding: $\mathrm{MMS}_n(v_i;M)$, the maximum over ordered partitions of $M$ into $n$ possibly empty bundles of the minimum bundle value → LittleCharity.MMS.mms (v i) n univ, a supremum over labelings Fin m → Fin n of the minimum labelled bundle value; reason: a labeling is exactly an ordered partition into n possibly empty bundles; the index set is finite and nonempty for n ≥ 1, so the supremum is the maximum
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Theorem 1.3, p. 4 (PDF p. 4)

import Mathlib
import Definitions.Def_DSICHardRev_ValuationClasses
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Supplement

/-- Theorem 1.3 (XOS valuations; Li–Sun, STOC 2027 submission #580, p. 4): every instance with
`n ≥ 1` agents and XOS valuations on the goods `Fin m` (each `v_i` the maximum of finitely many,
at least one, nonnegative additive valuations) admits a `5/16`-MMS allocation: pairwise disjoint
bundles `A_i` with `v_i(A_i) ≥ (5/16) · MMS_n(v_i; M)`. -/
theorem theorem_1_3 (n : ℕ) (hn : 1 ≤ n) {m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, DSICHardRev.IsXOS (v i)) :
    ∃ A : Fin n → Finset (Fin m), IsAllocation A ∧
      ∀ i : Fin n, 5 / 16 * LittleCharity.MMS.mms (v i) n Finset.univ ≤ v i (A i) := by sorry

end SubadditiveMMS580.Amplification.Supplement
