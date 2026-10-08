-- Prove2me | Theorems.Thm_WardropTraffic_MeanSpeed_time_mean_second_moment
-- name    : WardropTraffic.MeanSpeed.time_mean_second_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:44.628018+00:00
-- url     : https://prove2.me/theorems/dfc8e8a4-ff23-4fb7-b535-729d86feae49
-- title:
--   Appendix II, p. 356 — time mean as the space-frequency second moment divided by space mean
-- statement:
--   In a finite traffic stream with positive flows $q_i$ and speeds $v_i$, let $f'_i=k_i/K$ be the frequencies in space and $\bar v_s$ the space-mean speed. Then the time-mean speed is
--
--   $$\bar v_t=\frac{\sum_{i=1}^{C}f'_i v_i^2}{\bar v_s}.$$
--
--   This is the intermediate identity of Appendix II that links the two sampling distributions before the variance is introduced.
--
--   **Formalization Note** At least one stream and positive flow and speed in every stream ensure that $Q$, $K$, and $\bar v_s$ are positive.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 356, Appendix II, third display in the derivation

import Mathlib
import Definitions.Def_WardropTraffic_MeanSpeed_Setting

namespace WardropTraffic.MeanSpeed

theorem time_mean_second_moment {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    timeMean q v = (∑ i, spaceFreq q v i * v i ^ 2) / spaceMean q v := by sorry

end WardropTraffic.MeanSpeed
