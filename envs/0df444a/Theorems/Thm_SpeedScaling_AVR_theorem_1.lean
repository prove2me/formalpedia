-- Prove2me | Theorems.Thm_SpeedScaling_AVR_theorem_1
-- name    : SpeedScaling.AVR.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:55.993192+00:00
-- url     : https://prove2.me/theorems/462c2ad1-b08c-4d57-80e8-4b477e350c2a
-- title:
--   Theorem 1 — speed on a critical interval
-- statement:
--   Let $I^*=[z,z']$ be a critical interval for a job instance, and let $S$ be an energy-minimizing feasible schedule. Suppose the power function is strictly convex and nondecreasing on nonnegative speeds. Then, almost everywhere in the scheduling window, the processor speed is at most $g(I^*)$, and almost everywhere on $I^*$ it equals $g(I^*)$:
--   $$s(t)\le g(I^*)\quad\text{a.e. on }[t_0,t_1],\qquad s(t)=g(I^*)\quad\text{a.e. on }I^*.$$
--
--   This identifies the maximum speed segment of an optimum. The printed theorem says only “convex”; strict convexity and monotonicity are added because its literal claim fails for linear or decreasing power functions. The quadratic power used later satisfies both.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 375, Theorem 1.

import Definitions.Def_SpeedScaling_AVR_Model

namespace SpeedScaling.AVR
open MeasureTheory

theorem theorem_1 (P : ℝ → ℝ) (hP : StrictConvexOn ℝ (Set.Ici 0) P)
    (hPm : MonotoneOn P (Set.Ici 0)) {n : ℕ} (J : Instance n)
    (z z' : ℝ) (hI : IsCriticalInterval J z z') (S : Schedule n)
    (hS : IsOptimal P J S) :
    (∀ᵐ t ∂(volume.restrict (Set.Icc J.t0 J.t1)), S.s t ≤ intensity J z z') ∧
    (∀ᵐ t ∂(volume.restrict (Set.Icc z z')), S.s t = intensity J z z') := by sorry

end SpeedScaling.AVR
