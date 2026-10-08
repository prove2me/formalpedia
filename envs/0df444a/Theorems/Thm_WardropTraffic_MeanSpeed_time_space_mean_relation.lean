-- Prove2me | Theorems.Thm_WardropTraffic_MeanSpeed_time_space_mean_relation
-- name    : WardropTraffic.MeanSpeed.time_space_mean_relation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:58.291007+00:00
-- url     : https://prove2.me/theorems/04cfb5e1-9aa9-4096-be9b-19b0cfd643f9
-- title:
--   (6), p. 330 and Appendix II, p. 356 — time mean exceeds space mean by space variance divided by space mean
-- statement:
--   Consider $C\ge1$ subsidiary traffic streams, each with positive flow $q_i$ and positive speed $v_i$. Let $\bar v_t$ and $\bar v_s$ be the time-mean and space-mean speeds, and let $\sigma_s^2$ be the variance of the space distribution defined in equation (7). Wardrop's relation (6), together with its equality condition, is
--
--   $$\bar v_t=\bar v_s+\frac{\sigma_s^2}{\bar v_s},\qquad \bar v_s\le\bar v_t,\qquad \bar v_t=\bar v_s\ \Longleftrightarrow\ v_i=v_j\text{ for all }i,j.$$
--
--   Thus the two means agree exactly when there is no variation among the constituent stream speeds. The result explains why measurements made at a road point and measurements of vehicles occupying a stretch of road report different averages.
--
--   **Formalization Note** The variance is defined by the independent weighted formula (7), rather than by rearranging (6). Positivity of the number of streams, every flow, and every speed rules out zero denominators and makes the equality condition range exactly over present streams.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), pp. 330–331, (6)–(7) and strictness sentence; p. 356, Appendix II, closing sentence

import Mathlib
import Definitions.Def_WardropTraffic_MeanSpeed_Setting

namespace WardropTraffic.MeanSpeed

theorem time_space_mean_relation {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    timeMean q v = spaceMean q v + spaceVar q v / spaceMean q v ∧
      spaceMean q v ≤ timeMean q v ∧
      (timeMean q v = spaceMean q v ↔ ∀ i j, v i = v j) := by sorry

end WardropTraffic.MeanSpeed
