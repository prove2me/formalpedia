-- Prove2me | Theorems.Thm_WardropTraffic_MeanSpeed_space_frequencies
-- name    : WardropTraffic.MeanSpeed.space_frequencies
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:10.750131+00:00
-- url     : https://prove2.me/theorems/8fa43a7a-d021-48ef-85b6-2f9c7f8d2e5e
-- title:
--   Appendix II, p. 356 — the centered space-frequency sum is zero
-- statement:
--   Let $f'_i=k_i/K$ be the space frequency of stream $i$ in a finite traffic stream with positive flows and speeds, and let $\bar v_s$ be the space-mean speed. Appendix II uses the centered-frequency identity
--
--   $$\sum_{i=1}^{C} f'_i(v_i-\bar v_s)=0.$$
--
--   The identity removes the cross term when the squared speeds are expanded around the space mean.
--
--   **Formalization Note** The theorem includes $C\ge1$ and positive flows and speeds, which ensure $K>0$ and make the frequencies genuine weights.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 356, Appendix II, bracketed centered-frequency identity

import Mathlib
import Definitions.Def_WardropTraffic_MeanSpeed_Setting

namespace WardropTraffic.MeanSpeed

theorem space_frequencies {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    (∑ i, spaceFreq q v i * (v i - spaceMean q v)) = 0 := by sorry

end WardropTraffic.MeanSpeed
