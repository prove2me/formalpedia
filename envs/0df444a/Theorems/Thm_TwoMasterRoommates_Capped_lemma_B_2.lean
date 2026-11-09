-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_lemma_B_2
-- name    : TwoMasterRoommates.Capped.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:43:25.435623+00:00
-- url     : https://prove2.me/theorems/a1ad5947-44ca-430b-a6a0-0fa4eaf7fcaa
-- title:
--   Lemma B.2 (= 3.1) — quality-preserving internal normalization
-- statement:
--   For every capped weakly stable perfect matching $M$ of a two-master instance $I$, there is another solution $M'$ with the same attained quality at every identity. Every cross-class edge and every internal edge with unequal endpoint own-master ranks is retained, and every other identity is re-paired only with a partner of its own class and own-master tier. After those endpoints are removed, each remaining $A$ $a$-tier is paired consecutively in $(b,\mathrm{ID})$ order, and each remaining $B$ $b$-tier in $(a,\mathrm{ID})$ order:
--
--   $$Q(I,M')=Q(I,M).$$
--
--   The sorting is separate in each own-master tier; it never sorts all internal identities together. The normal-form predicate specifies the first–second, third–fourth pairs concretely, with even list length. The resulting matching still meets every personal cap and has no original blocker. This provides exactly the cap-safe normalization used in the scan.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - encoding: finite identity populations with arbitrary personal caps → finite labelled types, fixed-point-free involutions, and WithTop upper caps; reason: labels do not restrict populations; top is an infinite cap and every blocking comparison remains original and strict
--   - encoding: any fixed identity convention inside foreign-rank ties → the natural order on Fin n breaks sorting ties; reason: this chooses among equal-quality matchings without refining preferences
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 13 (PDF p. 14), Lemma B.2; pp. 4–5 (PDF pp. 5–6), Lemma 3.1

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_NormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- Lemma B.2 (= Lemma 3.1): per-tier pairing, preserving each quality and each fixed edge;
the remaining identities are re-paired only inside their own class and own-rank tier. -/
theorem lemma_B_2 {R : Type} [LinearOrder R] {n : ℕ}
    (I : Instance R n) (M : Fin n → Fin n) (hM : IsSolution I M) :
    ∃ M', IsSolution I M' ∧ Q I M' = Q I M ∧
      (∀ v, Keep I M v → M' v = M v) ∧ (∀ v, ¬ Keep I M v → ¬ Keep I M' v) ∧
      NormalForm I M' := by sorry

end TwoMasterRoommates.Capped
