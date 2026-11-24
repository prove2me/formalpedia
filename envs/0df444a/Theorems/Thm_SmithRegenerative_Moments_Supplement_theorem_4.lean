-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_Supplement_theorem_4
-- name    : SmithRegenerative.Moments.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:46:14.508826+00:00
-- url     : https://prove2.me/theorems/5e3569f6-2d24-428b-bd64-f7cfd4bb0f7b
-- title:
--   Theorem 4 — a non-null α-set forces finite mean recurrence
-- statement:
--   Let the renewal sequence and measurable state process share the probability measure $P_z$. If a measurable set $A$ is an $\alpha$-set and is non-null, then
--   $$P_z(t_0<\infty)>0,\qquad \mu_1<\infty.$$
--   The hypothesis means failure of convergence to zero, and does not presume an existing positive limit. This criterion detects a non-null regeneration event from an eventual lower bound on the chance of another regeneration.
--
--   Differences from the source:
--   - generalization: Theorem 4 follows Definitions 4 and 5 for a process sharing the regeneration sequence. → A measurable state process on the delayed-renewal probability space; no equilibrium representation is required.; reason: These are precisely the data used in the probability inequalities (3·7·3); neither the statement nor its proof assumes the equilibrium representation.
--   - encoding: Real time and the paper’s distribution-function notation. → Probability measures with explicit mass at infinity and real-time limits; lattice sampling alone uses natural indices.; reason: Preserve defective laws, infinite means and the exact asymptotic domain without total-function defaults.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 19, Theorem 4

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_Supplement_Equilibrium

namespace SmithRegenerative.Moments.Supplement

open MeasureTheory Filter Topology

/-- Smith (1955), Theorem 4, p. 19; Definitions 4–5, (3·7·1)–(3·7·2).
Formalization Note: a measurable state process on the same probability space is
sufficient; no equilibrium condition is used or imposed by this theorem. Both
positive finite-entry probability and finite cycle mean are conclusions. -/
theorem theorem_4 {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (R : ExtendedRenewal Ω Z) (x : ℝ → Ω → X) (hx : ∀ t, Measurable (x t))
    (z : Z) (h : ∃ A : Set X, MeasurableSet A ∧ AlphaSet R x z A ∧ NonNull R x z A) :
    0 < R.K z (Set.Iio ⊤) ∧ extendedMean R.F < ⊤ := by sorry

end SmithRegenerative.Moments.Supplement
