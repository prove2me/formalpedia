-- Prove2me | Theorems.Thm_RobustMNL_Dynamic_dynamic_robust_rewrite
-- name    : RobustMNL.Dynamic.dynamic_robust_rewrite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:33.792004+00:00
-- url     : https://prove2.me/theorems/2939791e-b3c9-4acd-b8e0-4778e75f0fa3
-- title:
--   (Dynamic Robust), p. 16, second line — J_t(x) = max_S min_v Σ φ_i(S, v)(r_i − ΔJ_{t+1}(x)) + J_{t+1}(x)
-- statement:
--   In the robust capacity-allocation model, let $1 \le t \le T$ and $x \ge 1$. Then the Bellman equation can be rewritten through the marginal value of capacity $\Delta J_{t+1}(x) = J_{t+1}(x) - J_{t+1}(x-1)$:
--   $$J_t(x) = \max_{S_t \subseteq \mathcal A}\ \min_{v_t \in \mathcal V_t} \Big\{ \sum_{i\in S_t} \phi_i(S_t, v_t)\,\big(r_i - \Delta J_{t+1}(x)\big) \Big\} + J_{t+1}(x).$$
--
--   This form displays one period of the dynamic problem as a static robust assortment problem with revenues $r_i - \Delta J_{t+1}(x)$, plus the value of keeping the capacity.
--
--   **Formalization Note** $J$ is defined by the first line of (Dynamic Robust); this statement is its second line. The minimum is a real infimum over `V t`, compact, nonempty and positive by the standing hypothesis; the maximum is over all $2^n$ assortments.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, (Dynamic Robust), second line, p. 16

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_ValueFunction

namespace RobustMNL.Dynamic

theorem dynamic_robust_rewrite {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x) :
    J T V r t x =
      (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty
          (fun S => sInf ((fun p => ∑ i ∈ S, choiceProb S p i *
              (r i - marginalValue T V r (t + 1) x)) '' V t))
        + J T V r (t + 1) x := by sorry

end RobustMNL.Dynamic
