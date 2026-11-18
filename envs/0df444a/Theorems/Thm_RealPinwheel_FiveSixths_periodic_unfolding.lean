-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_periodic_unfolding
-- name    : RealPinwheel.FiveSixths.periodic_unfolding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:50:37.83414+00:00
-- url     : https://prove2.me/theorems/a8430f84-a5f4-474d-9dcb-e11483d14bc9
-- title:
--   Binary unfolding preserves a doubled period
-- statement:
--   Let $S$ be a valid periodic schedule of an ordered real-period instance $A$, with positive period $L$. Replace one task of period $a_j$ by two distinct tasks of period $2a_j$, then reorder the periods. The resulting instance admits a valid schedule $T$ satisfying
--
--   $$T(t+2L)=T(t)\quad(t\ge0).$$
--
--   This is the periodic unfolding observation in Section 2. It supplies the factor of two in the quantitative period bound; $2L$ is a period, whether or not it is least.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, A Simple Computer-Assisted Proof of the 5/6-Bound for Real-Period Pinwheel Scheduling, STOC 2027 submission #885, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Section 2, periodic unfolding paragraph, printed p. 7 (PDF p. 8)

import Definitions.Def_RealPinwheel_FiveSixths_Transformations
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.periodic_unfolding {n : ℕ} (A : Instance n) (S : ℕ → Fin n) (hS : Valid A.period S)
    (j : Fin n) (L : ℕ) (hL : 0 < L) (hper : ∀ t, S (t + L) = S t) :
    ∃ T : ℕ → Fin (unfoldedLabels A.period j 2).length,
      Valid (unfoldedPeriods A.period j 2) T ∧ Periodic T (2 * L) := by sorry
