-- Prove2me | Theorems.Thm_SingleOrSample_supporting_prices
-- name    : SingleOrSample.supporting_prices
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:48:01.898204+00:00
-- url     : https://prove2.me/theorems/83d4fc67-3228-4ccd-b6ac-8dbf9e1b63a9
-- title:
--   §4.2.2 — supporting prices
-- statement:
--   Let $v$ be a monotone, normalized, submodular valuation and $P$ a labelling of the goods into $n$ bundles with $v(P_h)\ge1$ for every $h$. For any orderings of the bundles, the prices $w_e=a_e/v(P_h)$ satisfy, for every bundle $P_h$,
--   $$\sum_{e\in P_h}w_e=1,\qquad 0\le w_e\le1\ (e\in P_h),\qquad \sum_{e\in Q}w_e\le v(Q)\ \text{ for every }Q\subseteq P_h.$$
--
--   The last inequality is the one that transfers the surviving weight of a bundle into its surviving value.
--
--   Differences from the source:
--   - generalization: (P_1,…,P_n) an MMS-defining partition for a normalized agent → any labelling with v(P_h) ≥ 1 for all h; reason: an MMS-defining partition under MMS = 1 has this property (Definition 3, p.6), and it is all the proof uses
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §4.2.2, p.15

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SingleOrSample_IsValuation
import Definitions.Def_SingleOrSample_chainPrice

namespace SingleOrSample

/-- **Supporting prices** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §4.2.2, p.15). For a labelling `P` of the goods with `v(P_h) ≥ 1` for
every `h`, and any orderings of the bundles, the prices `w_e = a_e / v(P_h)` satisfy `∑_{e ∈ P_h} w_e = 1`,
`0 ≤ w_e ≤ 1` and `∑_{e ∈ Q} w_e ≤ v(Q)` for every `Q ⊆ P_h`.

**Formalization Note.** The hypothesis `1 ≤ v(P_h)` is what an MMS-defining partition has under `MMS = 1`
(Definition 3, p.6); it is more general than taking such a partition. -/
theorem supporting_prices {m n : ℕ} (v : Finset (Fin m) → ℝ) (hv : IsValuation v)
    (hsub : SubsamplingSM.Offline.IsSubmodular v) (P : Fin m → Fin n)
    (hP : ∀ b, 1 ≤ v (bundle P b)) (order : Fin n → List (Fin m))
    (hnodup : ∀ b, (order b).Nodup) (hmem : ∀ b e, e ∈ order b ↔ P e = b) (b : Fin n) :
    ∑ e ∈ bundle P b, chainPrice v P order e = 1 ∧
    (∀ e ∈ bundle P b, 0 ≤ chainPrice v P order e ∧ chainPrice v P order e ≤ 1) ∧
    ∀ Q ⊆ bundle P b, ∑ e ∈ Q, chainPrice v P order e ≤ v Q := by sorry

end SingleOrSample
