-- Prove2me | Theorems.Thm_RobustMNL_Dynamic_marginalValue_antitone_time
-- name    : RobustMNL.Dynamic.marginalValue_antitone_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:43.264656+00:00
-- url     : https://prove2.me/theorems/ddda93dd-3b5e-4550-acf8-ef95bd030ccc
-- title:
--   Theorem 4.1, p. 16, second inequality — ΔJ_{t+1}(x) ≤ ΔJ_t(x): the marginal value of capacity decreases over time
-- statement:
--   In the robust capacity-allocation model, for every period $1 \le t \le T$ and every capacity level $x \ge 1$,
--   $$\Delta J_{t+1}(x) \le \Delta J_t(x).$$
--   At $t = T$, where $J_{T+1} \equiv 0$, this says $J_T$ is nondecreasing in capacity.
--
--   The second half of Theorem 4.1: as the horizon runs out, a unit of capacity is worth less. It gives the nonnegative increment $\Delta J_{t+1}(x) - \Delta J_{t+2}(x)$ used in the second part of Theorem 4.3.
--
--   **Formalization Note** As for the first inequality, $x = 0$ is excluded (the paper's "$x \in \{0, \dots, C\}$" includes an undefined $\Delta J_t(0)$) and $x$ has no upper bound. Revenues are arbitrary reals.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Theorem 4.1 (second inequality), p. 16; proof in Appendix A, p. 32

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_ValueFunction

namespace RobustMNL.Dynamic

theorem marginalValue_antitone_time {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x) :
    marginalValue T V r (t + 1) x ≤ marginalValue T V r t x := by sorry

end RobustMNL.Dynamic
