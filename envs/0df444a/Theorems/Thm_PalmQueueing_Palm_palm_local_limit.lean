-- Prove2me | Theorems.Thm_PalmQueueing_Palm_palm_local_limit
-- name    : PalmQueueing.Palm.palm_local_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T21:28:15.703355+00:00
-- url     : https://prove2.me/theorems/d769e77d-d14f-43f8-9b46-6141b984e665
-- title:
--   Theorem 1.5.1 — conditioning at a point: Palm probability as a local limit
-- statement:
--   **Theorem 1.5.1.** The local interpretation of Palm probability:
--   $$ \lim_{t \to 0}\; \sup_{A \in \mathcal{F}}\;
--   \big| P^0_N(A) - P(\theta_{T_1} \in A \mid T_1 \le t) \big| \;=\; 0 . \tag{1.5.3} $$
--
--   The Palm probability is the limit of conditioning on there being a point of the process in a
--   shrinking window to the right of the origin — this is the statement that makes "what an arriving
--   customer sees" precise, and it is why $P^0_N$ deserves to be read as the law seen from a typical
--   point.
--
--   The supremum over $A \in \mathcal{F}$ sits **inside** the limit: the convergence is uniform over
--   all measurable events. That uniformity is what the proof's Dobrushin estimate
--   ($\lim_{t\to 0} \lambda t / P(T_1 \le t) = 1$, §1.5.1) buys, and a pointwise limit would be a
--   strictly weaker statement. The $\varepsilon$-$\delta$ form of the statement says exactly this: one
--   $\delta$ serves every $A$ at once.
--
--   The proof rewrites $P(\theta_{T_1} \in A \mid T_1 \le t)$ using (1.2.28), obtains
--   $P(T_1 \le t, \theta_{T_1} \in A) = \lambda \int_0^t P^0_N(u < -T_{-1}, A)\,du$, and concludes from
--   $P^0_N(u \ge -T_{-1}) \to 0$ as $u \to 0$.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 45, Theorem 1.5.1, Eq. (1.5.3)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Theorem 1.5.1: conditioning at a point (§1.5.2, p.45)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.5.1** (§1.5.2, p.45), the local aspect of Palm probability:

`(1.5.3)  lim_{t → 0} sup_{A ∈ F} | P⁰_N(A) - P(θ_{T₁} ∈ A | T₁ ≤ t) | = 0`.

The Palm probability is the limit of conditioning on there being a point in a shrinking window to
the right of the origin — the statement that makes "what an arriving customer sees" precise. The
supremum over `A ∈ F` is inside the limit and is not decorative: the convergence is **uniform over
all measurable events**, which is what the proof's Dobrushin estimate (§1.5.1) buys and what a
pointwise limit would not give. The `ε`-`δ` form below says exactly that: one `δ` serves every `A`
at once. -/
theorem palm_local_limit (S : PalmSetting Ω)
    (hshift : Measurable fun ω => S.θ (S.N.T 1 ω) ω) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ A : Set Ω, MeasurableSet A →
        |(S.P0 A).toReal
            - (S.P ({ω | S.θ (S.N.T 1 ω) ω ∈ A} ∩ {ω | S.N.T 1 ω ≤ t})).toReal
                / (S.P {ω | S.N.T 1 ω ≤ t}).toReal| ≤ ε := by sorry

end PalmQueueing.Palm
