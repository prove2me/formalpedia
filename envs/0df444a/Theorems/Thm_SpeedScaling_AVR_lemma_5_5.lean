-- Prove2me | Theorems.Thm_SpeedScaling_AVR_lemma_5_5
-- name    : SpeedScaling.AVR.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:21.262605+00:00
-- url     : https://prove2.me/theorems/28950deb-b679-41dc-881c-8fc73e8e6964
-- title:
--   Lemma 5.5 — nesting
-- statement:
--   For every consistent choice of A-job deadlines $x$, there is another consistent choice $x'$ whose overlapping A-job windows are properly nested in A order and
--   $$F_A(x)\le F_A(x').$$
--
--   This is the nesting reduction used before the tree-induced matrix bound.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 380, Lemma 5.5.

import Definitions.Def_SpeedScaling_AVR_Consistent

namespace SpeedScaling.AVR

theorem lemma_5_5 (D : ExecData) (x : Fin D.m → ℝ)
    (hx : ConsistentA D x) :
    ∃ x' : Fin D.m → ℝ, ConsistentA D x' ∧ NestedA D x' ∧ FA D x ≤ FA D x' := by sorry

end SpeedScaling.AVR
