-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_proposition_4_4
-- name    : SubadditiveMMS580.Amplification.Supplement.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:57:27.036224+00:00
-- url     : https://prove2.me/theorems/2716530d-c927-418d-8592-a6982001ee85
-- title:
--   Proposition 4.4 — for $q>n\ge2$, $\mathcal Q_q$ instances admit $\min\{1/4,2(q-n)/(7q-6n)\}$-MMS allocations
-- statement:
--   Let $q>n\ge2$ be integers and
--   $$\alpha=\min\Big\{\frac14,\ \frac{2(q-n)}{7q-6n}\Big\}.$$
--   Every instance with $n$ agents and valuations $v_1,\dots,v_n\in\mathcal Q_q$ on a finite set $M$ of goods admits an $\alpha$-MMS allocation: pairwise disjoint bundles $A_i\subseteq M$ with $v_i(A_i)\ge\alpha\cdot\mathrm{MMS}_n(v_i;M)$ for every agent $i$.
--
--   It gives the last two branches of $\rho$ in Theorem 1.2.
--
--   Differences from the source:
--   - reading: 'Algorithm 3 returns an α-MMS allocation on the working instance. Consequently, every instance with valuations in Q_q admits an α-MMS allocation' → the existence of an α-MMS allocation for every instance with valuations in Q_q; reason: the working instance is one such instance, so its claim is a special case of the stated conclusion; Algorithm 3 is the procedure of the proof, not a separate mathematical object
--   - encoding: partitions $(C_1,\dots,C_t)\in\Pi(S,t)$ into $t\le q$ nonempty groups (Definition 2.1) → 1 ≤ t ≤ q and C : Fin t → Finset (Fin m) with nonempty, pairwise disjoint members whose union is S; reason: the same ordered partitions
--   - encoding: valuations $v_i : 2^M \to \mathbb R_{\ge 0}$, normalized and monotone → real set functions on Finset (Fin m) with the published IsNormalized and IsMonotone predicates; reason: normalization and monotonicity give nonnegativity, so the instances are the same
--   - encoding: an allocation (pairwise disjoint bundles, goods may stay unassigned) → IsAllocation A (pairwise disjoint Finset bundles indexed by Fin n); reason: the source allows partial allocations (§2.1, p. 8); completing one cannot lower a monotone value
--   - encoding: $\mathrm{MMS}_n(v_i;M)$, the maximum over ordered partitions of $M$ into $n$ possibly empty bundles of the minimum bundle value → LittleCharity.MMS.mms (v i) n univ, a supremum over labelings Fin m → Fin n of the minimum labelled bundle value; reason: a labeling is exactly an ordered partition into n possibly empty bundles; the index set is finite and nonempty for n ≥ 1, so the supremum is the maximum
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Proposition 4.4, p. 26 (PDF p. 26)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Supplement

/-- Proposition 4.4 (Li–Sun, STOC 2027 submission #580, p. 26): for integers `q > n ≥ 2`, with
`α = min {1/4, 2(q − n)/(7q − 6n)}`, every instance with `n` agents and valuations in `Q_q` on
the goods `Fin m` admits an `α`-MMS allocation. -/
theorem proposition_4_4 (n q : ℕ) (hn : 2 ≤ n) (hnq : n < q) {m : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ) (hv : ∀ i, IsQPartitioning q (v i)) :
    ∃ A : Fin n → Finset (Fin m), IsAllocation A ∧
      ∀ i : Fin n, min (1 / 4) (2 * ((q : ℝ) - n) / (7 * q - 6 * n)) *
        LittleCharity.MMS.mms (v i) n Finset.univ ≤ v i (A i) := by sorry

end SubadditiveMMS580.Amplification.Supplement
