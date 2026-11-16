-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_lemma_4_1
-- name    : SubadditiveMMS580.Amplification.Supplement.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:54:46.127386+00:00
-- url     : https://prove2.me/theorems/b1389f38-6fd5-481e-940d-c43be5012470
-- title:
--   Lemma 4.1 — $\mathcal Q_q$ is closed under restriction, nonnegative scaling and capping
-- statement:
--   Let $q\ge2$ and let $v\in\mathcal Q_q$ be a $q$-partitioning valuation on the goods $M$. Then:
--
--   1. (**restriction**) for every subset $R\subseteq M$, $v$ satisfies the $\mathcal Q_q$ conditions with ground set $R$, i.e. the restriction of $v$ to $2^R$ is $q$-partitioning;
--   2. (**scaling**) for every $c\ge0$, the valuation $S\mapsto c\,v(S)$ belongs to $\mathcal Q_q$;
--   3. (**capping**) for every $C\ge0$, the capped valuation
--   $$v^C(S)=\min\{v(S),C\}$$
--   belongs to $\mathcal Q_q$.
--
--   Capping is what makes capped social welfare usable as a potential in the grouping construction of Proposition 4.3.
--
--   Differences from the source:
--   - encoding: partitions $(C_1,\dots,C_t)\in\Pi(S,t)$ into $t\le q$ nonempty groups (Definition 2.1) → 1 ≤ t ≤ q and C : Fin t → Finset (Fin m) with nonempty, pairwise disjoint members whose union is S; reason: the same ordered partitions
--   - encoding: valuations $v_i : 2^M \to \mathbb R_{\ge 0}$, normalized and monotone → real set functions on Finset (Fin m) with the published IsNormalized and IsMonotone predicates; reason: normalization and monotonicity give nonnegativity, so the instances are the same
--   - encoding: the restriction of v to a subset R of goods (a valuation on 2^R) → IsQPartitioningOn q R v: normalization, monotonicity on subsets of R, and supporting prices for partitions of subsets of R; reason: the restriction takes the same values on subsets of R, so these are exactly its Q_q conditions
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Lemma 4.1, p. 21 (PDF p. 21)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Supplement

/-- Lemma 4.1 (Li–Sun, STOC 2027 submission #580, p. 21): for `q ≥ 2` and `v ∈ Q_q`,
(a) for every `R ⊆ M` the valuation satisfies the `Q_q` conditions on the ground set `R`
(restriction), (b) `c · v ∈ Q_q` for every `c ≥ 0` (scaling), and (c) the capped valuation
`v^C(S) = min {v(S), C}` belongs to `Q_q` for every `C ≥ 0` (capping). -/
theorem lemma_4_1 {m : ℕ} (q : ℕ) (hq : 2 ≤ q) (v : Finset (Fin m) → ℝ)
    (hv : IsQPartitioning q v) :
    (∀ R : Finset (Fin m), IsQPartitioningOn q R v) ∧
    (∀ c : ℝ, 0 ≤ c → IsQPartitioning q (fun S => c * v S)) ∧
    (∀ C : ℝ, 0 ≤ C → IsQPartitioning q (capped v C)) := by sorry

end SubadditiveMMS580.Amplification.Supplement
