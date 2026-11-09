-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_lemma_4_1
-- name    : TwoMasterRoommates.Capped.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:43:38.50325+00:00
-- url     : https://prove2.me/theorems/1fac5de6-5e78-4c44-a27d-045319475aa4
-- title:
--   Lemma 4.1 — incompatible wrong activity and unique own activity
-- statement:
--   Let $I$ be a two-master instance and $M$ any partner map with no original blocking pair. At any cuts $(i,j)$, no wrong-active $A$ identity and wrong-active $B$ identity coexist. In addition, there is at most one own-active identity in each observer class:
--
--   $$|\{v\in A:a(v)\le i<Q_v\}|\le1,\qquad |\{v\in B:b(v)\le j<Q_v\}|\le1.$$
--
--   An $A$ identity is wrong-active when $a(v)>i$, $b(v)\le j$, and $Q_v>i$; exchange the two masters for $B$. All three assertions use strict improvement and include equality at each cut. These incompatibilities constrain the scan without imposing any bound on tie sizes.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - generalization: a stable matching → any partner map without a blocker, with no perfection or cap assumptions; reason: the two strict inequalities alone force each forbidden pair to block
--   - encoding: finite identity populations with arbitrary personal caps → finite labelled types, fixed-point-free involutions, and WithTop upper caps; reason: labels do not restrict populations; top is an infinite cap and every blocking comparison remains original and strict
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 6 (PDF p. 7), Lemma 4.1; p. 13 (PDF p. 14), §B.1

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_NormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- Lemma 4.1 without the unused perfection and cap assumptions. -/
theorem lemma_4_1 {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (M : Fin n → Fin n) (h : ∀ u v, ¬ Blocks I M u v) (i j : R) :
    (¬ ∃ u v, I.isA u = true ∧ WrongActive I M i j u ∧
      I.isA v = false ∧ WrongActive I M i j v) ∧
    (∀ u v, I.isA u = true → I.isA v = true → OwnActive I M i j u →
      OwnActive I M i j v → u = v) ∧
    (∀ u v, I.isA u = false → I.isA v = false → OwnActive I M i j u →
      OwnActive I M i j v → u = v) := by sorry

end TwoMasterRoommates.Capped
