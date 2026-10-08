-- Prove2me | Theorems.Thm_WardropTraffic_MeanSpeed_flow_concentration
-- name    : WardropTraffic.MeanSpeed.flow_concentration
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:54.469439+00:00
-- url     : https://prove2.me/theorems/55e1684f-92f7-4379-ba59-ea0e6a7c3050
-- title:
--   (4)–(5), p. 330 — flow equals concentration times speed, and Q = K v̄ₛ
-- statement:
--   Let $C\ge1$ subsidiary traffic streams have positive flows $q_i$ and speeds $v_i$. Put $k_i=q_i/v_i$, $Q=\sum_i q_i$, $K=\sum_i k_i$, and $\bar v_s=(\sum_i k_i v_i)/K$. Then each stream satisfies equation (4), and the totals satisfy equation (5):
--
--   $$k_i v_i=q_i\quad(1\le i\le C),\qquad Q=K\bar v_s.$$
--
--   This is the flow–concentration identity used to replace the time distribution by the space distribution in Appendix II.
--
--   **Formalization Note** The positive-flow and positive-speed conditions, together with $C\ge1$, make every denominator in the model nonzero.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 330, (4)–(5)

import Mathlib
import Definitions.Def_WardropTraffic_MeanSpeed_Setting

namespace WardropTraffic.MeanSpeed

theorem flow_concentration {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    (∀ i, conc q v i * v i = q i) ∧
      totalFlow q = totalConc q v * spaceMean q v := by sorry

end WardropTraffic.MeanSpeed
