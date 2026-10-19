-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_lemma_6
-- name    : WaitTimePricing.Existence.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:26.405888+00:00
-- url     : https://prove2.me/theorems/4080e9a2-6c27-4ef9-b664-810cdf56f674
-- title:
--   Lemma 6 — $V^{\bar g}_{2^j}$ is decreasing, concave and $\bar g$-Lipschitz on $[0,\bar w+C]$
-- statement:
--   For every positive integer $j$:
--
--   1. $V^{\bar g}_{2^j}$ is nonincreasing and concave on $[0,\bar w+C]$;
--   2. $V^{\bar g}_{2^j}$ is Lipschitz with constant $\bar g$ there:
--   $$|V^{\bar g}_{2^j}(x)-V^{\bar g}_{2^j}(y)|\le\bar g\,|x-y|\qquad(x,y\in[0,\bar w+C]).$$
--
--   The uniform Lipschitz bound is what lets the approximations converge uniformly (Proposition 6).
--
--   **Formalization Note** "Decreases" means nonincreasing. The Lipschitz bound is stated on $[0,\bar w+C]$, the interval of the paper's proof.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 37, Lemma 6 (Appendix B, proof of Proposition 6)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 37, Lemma 6 (Appendix B, proof of Proposition 6).

Given any positive integer `j`: (1) `V^ḡ_{2^j}(w)` decreases and is concave in `w` on
`[0, w̄ + C]`; (2) `V^ḡ_{2^j}(w)` is Lipschitz continuous in `w` with Lipschitz constant `ḡ`.

**Formalization Note.** "Decreases" is `AntitoneOn` (the proof shows slopes `−ḡ + K ≤ 0`). The
Lipschitz bound is written with absolute values on `[0, w̄ + C]`, the interval of the proof
(p. 37). `ḡ` is `gbar`, whose convergence is Proposition 5. -/
theorem lemma_6 (M : Model) (hM : M.Standing) (obj : Objective) :
    ∀ j : ℕ, 1 ≤ j →
      AntitoneOn (VgN M obj (gbar M obj) (2 ^ j)) (Icc 0 (wbar M + M.C)) ∧
      ConcaveOn ℝ (Icc 0 (wbar M + M.C)) (VgN M obj (gbar M obj) (2 ^ j)) ∧
      ∀ x ∈ Icc 0 (wbar M + M.C), ∀ y ∈ Icc 0 (wbar M + M.C),
        |VgN M obj (gbar M obj) (2 ^ j) x - VgN M obj (gbar M obj) (2 ^ j) y|
          ≤ gbar M obj * |x - y| := by sorry

end WaitTimePricing.Existence
