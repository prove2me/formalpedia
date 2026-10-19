-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_6
-- name    : WaitTimePricing.Existence.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:39.799981+00:00
-- url     : https://prove2.me/theorems/408ef608-7962-444b-9069-959fe96697f3
-- title:
--   Proposition 6 — $V^{\bar g}_{2^j}\to V^{\bar g}$ uniformly; $V^{\bar g}$ concave, decreasing, Lipschitz
-- statement:
--   For every $w\in[0,\bar w+C]$ the sequence $V^{\bar g}_{2^j}(w)$ converges, and $V^{\bar g}(w)=\lim_{j\to\infty}V^{\bar g}_{2^j}(w)$. Furthermore, on $[0,\bar w+C]$:
--
--   1. $V^{\bar g}_{2^j}\to V^{\bar g}$ uniformly;
--   2. $V^{\bar g}$ is concave and nonincreasing;
--   3. $V^{\bar g}$ is Lipschitz with constant $\bar g$:
--   $$|V^{\bar g}(x)-V^{\bar g}(y)|\le\bar g\,|x-y|.$$
--
--   $V^{\bar g}$ is the candidate relative value function of the optimality equations.
--
--   **Formalization Note** "Decreasing" means nonincreasing. The printed (iii) says only "Lipschitz continuous"; the constant $\bar g$ is the one the proof gives ((66), p. 38). $V^{\bar g}$ is defined as a pointwise limit with a default value; the first claim asserts the convergence.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 17, Proposition 6; p. 38, (66)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 17, Proposition 6.

For every `w ∈ [0, w̄ + C]` the sequence `V^ḡ_{2^j}(w)` has a limit `V^ḡ(w)`. Furthermore:
(i) `V^ḡ_{2^j} → V^ḡ` uniformly; (ii) `V^ḡ` is concave and decreasing; (iii) `V^ḡ` is Lipschitz
continuous on `[0, w̄ + C]`.

**Formalization Note.** `Vbar` is a pointwise `limUnder`; the first conjunct asserts the
convergence. Uniform convergence, concavity and monotonicity are on `[0, w̄ + C]`; "decreasing"
is `AntitoneOn`. The Lipschitz constant `ḡ` is the one the proof gives ((66), p. 38). -/
theorem proposition_6 (M : Model) (hM : M.Standing) (obj : Objective) :
    (∀ w ∈ Icc 0 (wbar M + M.C),
      Tendsto (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j) w) atTop (nhds (Vbar M obj w))) ∧
    TendstoUniformlyOn (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j)) (Vbar M obj) atTop
      (Icc 0 (wbar M + M.C)) ∧
    ConcaveOn ℝ (Icc 0 (wbar M + M.C)) (Vbar M obj) ∧
    AntitoneOn (Vbar M obj) (Icc 0 (wbar M + M.C)) ∧
    ∀ x ∈ Icc 0 (wbar M + M.C), ∀ y ∈ Icc 0 (wbar M + M.C),
      |Vbar M obj x - Vbar M obj y| ≤ gbar M obj * |x - y| := by sorry

end WaitTimePricing.Existence
