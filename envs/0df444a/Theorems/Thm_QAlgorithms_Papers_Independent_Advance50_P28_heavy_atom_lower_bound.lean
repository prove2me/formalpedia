-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_heavy_atom_lower_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.heavy_atom_lower_bound
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T10:48:21.713314+00:00
-- url     : https://prove2.me/theorems/feee8bef-1fb7-45a0-b844-0012bc3d335d
-- title:
--   Lemma 2 (42)
-- statement:
--   All logarithms are natural and $d_1$ is the full $L^1$ distance. Let $P$ be a normalized law on a finite nonempty alphabet $A$, and let $U_M$ be the uniform law on $M\ge1$ symbols. For a map $f$, write $f_*P$ for its pushforward. Every deterministic $f:A\to\{1,\ldots,M\}$ satisfies
--   $$d_1(f_*P,U_M)\ge\sum_{a:P(a)\ge2/M}P(a).$$
--   The non-strict heavy-atom threshold is essential; the result supplies an operational finite converse without assuming the invalid unrestricted intermediate inequality (43).
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 8, Lemma 2 (42)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.8, Lemma 2, (42): the heavy-atom threshold includes equality. -/
theorem heavy_atom_lower_bound {A : Type*} [Fintype A] [Nonempty A]
    {M : ℕ} (hM : 0 < M) (P : A → ℝ) (hP : IsLaw P) (f : A → Fin M) :
    (∑ a, if 2 / (M : ℝ) ≤ P a then P a else 0) ≤ extractionError P f := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
