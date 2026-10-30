-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_accumulated_exclusion
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.accumulated_exclusion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:00:17.100191+00:00
-- url     : https://prove2.me/theorems/e06c6b10-b77b-4d6c-939e-6b36d8b00642
-- title:
--   Lemma 10 / Eq.(43): exclusion under accumulated swaps (corrected index)
-- statement:
--   Let $k\ge1$, $k\le N$, and let $a,b$ be separately injective ordered lists in $\{1,\ldots,N\}$. Construct the swaps of Notation 5, allowing equal endpoints. For every $s=1,\ldots,k$,
--
--   $$L_{s-1}\cdots L_1(b_s)\notin\{a_1,\ldots,a_{s-1}\}.$$
--
--   This corrects the printed endpoint $a_{k-1}$ in Eq. (43) to $a_{s-1}$. The printed claim is false at $s=1$ with identical lists, while Eq. (44) and the summation argument use exactly the preceding entries. This correction requires independent moderation.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 10, Lemma 10 / Eq.(43): exclusion under accumulated swaps (corrected index)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF pp.10–11, Lemma 10, Eq.(43), CORRECTED: exclude a_1,...,a_(s-1).
Printed a_(k-1) is false for s=1; Eq.(44) and the summation proof force s-1. -/
theorem accumulated_exclusion (N k : ℕ) (hk : 1 ≤ k) (hNk : k ≤ N)
    (a b : MPBTPortSelection N k) (s : Fin k) :
    ∀ i : Fin k, i.val < s.val → accumulated a b s.val (b s) ≠ a i := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
