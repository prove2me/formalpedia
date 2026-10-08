-- Prove2me | Theorems.Thm_SpeedScaling_AVR_lemma_5_4
-- name    : SpeedScaling.AVR.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:40.149364+00:00
-- url     : https://prove2.me/theorems/4a68c26e-e6c0-4cf6-ae87-5a185de5ded5
-- title:
--   Lemma 5.4 — alignment
-- statement:
--   Fix the execution intervals, their speeds, and the A/B labels. For every consistent choice of A-job deadlines $x$, there is another consistent choice $x'$ whose A-job windows end at execution-interval boundaries and
--   $$F_A(x)\le F_A(x').$$
--
--   Thus aligned windows suffice when maximizing $F_A$ for fixed execution data.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 379, Lemma 5.4.

import Definitions.Def_SpeedScaling_AVR_Consistent

namespace SpeedScaling.AVR

theorem lemma_5_4 (D : ExecData) (x : Fin D.m → ℝ)
    (hx : ConsistentA D x) :
    ∃ x' : Fin D.m → ℝ, ConsistentA D x' ∧ AlignedA D x' ∧ FA D x ≤ FA D x' := by sorry

end SpeedScaling.AVR
