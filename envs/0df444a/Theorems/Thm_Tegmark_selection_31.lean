-- Prove2me | Theorems.Thm_Tegmark_selection_31
-- name    : Tegmark.selection_31
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T04:19:32.471705+00:00
-- url     : https://prove2.me/theorems/1fa83112-4d13-453f-b816-8f6c2795cf18
-- title:
--   Observers find themselves in (3 + 1) dimensions with conditional probability one
-- statement:
--   The Bayesian capstone of the letter (pages L69-L70). Ensemble theories predict a probability distribution over spacetime dimensionalities; the selection effect of observerhood collapses it. In a world ensemble in which observers exist with positive probability, and in which every observer world satisfies the predictability requirement — which forces exactly one time dimension — the stability requirement of at most three space dimensions, and the complexity requirement of at least three space dimensions, the probability of being an observer in a (3, 1)-dimensional world equals the probability of being an observer: conditional on being an observer, the dimensionality is (3, 1) with probability one, and the Bayesian prior probabilities over dimensionalities are completely irrelevant. The ensemble predicts that we should find ourselves inhabiting a (3 + 1)-dimensional spacetime with 100% certainty.
--
--   **Formalization Note** The four hypotheses are the letter's argumentative premises: observerhood with positive probability (we exist), and the three selection requirements on the observer worlds. The conclusion is the equality of the measure of the observer worlds inside the (3, 1) region with the measure of all observer worlds; the positive-probability hypothesis is carried so that the equality reads as the letter's conditional-probability statement. The requirements on the observer worlds are abstract hypotheses, not theorems of the mission: the letter is explicit that it has not attempted to rigorously demonstrate that observers are impossible for other dimensionalities. The milestones `predictable_m1` and `orbit_stability_31` are the mathematical content behind the predictability and stability premises.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, pp. L69-L70, L74-L75.

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble

namespace Tegmark

/-!
# Goal: observers find themselves in (3 + 1) dimensions

The Bayesian capstone of Tegmark 1997 (pp. L69-L70): ensemble
theories predict a probability distribution over spacetime
dimensionalities, and the selection effect of observerhood collapses
it. In a world ensemble in which observers exist with positive
probability and every observer world satisfies the predictability
requirement, the stability requirement of at most three space
dimensions, and the complexity requirement of at least three space
dimensions, the probability of being an observer in a "(3, 1)"
-dimensional world equals the probability of being an observer:
conditional on being an observer, the dimensionality is "(3, 1)"
with probability one, regardless of the prior distribution over
dimensionalities.
-/

/-- In a world ensemble whose observer worlds satisfy the
predictability requirement and have at most three and at least three
space dimensions, and in which observers exist with positive
probability, the probability of being an observer in a world with
three space dimensions and one time dimension equals the probability
of being an observer (Tegmark 1997, pp. L69-L70): the conditional
probability of the "(3, 1)" dimensionality given observerhood is
one. -/
theorem selection_31 {W : Type} [MeasurableSpace W] (𝒮 : WorldEnsemble W)
    (_hobs : 0 < 𝒮.μ 𝒮.hasObservers)
    (_hpred : ∀ w ∈ 𝒮.hasObservers, Predictable (𝒮.nOf w) (𝒮.mOf w))
    (_hstab : ∀ w ∈ 𝒮.hasObservers, 𝒮.nOf w ≤ 3)
    (_hcomp : ∀ w ∈ 𝒮.hasObservers, 3 ≤ 𝒮.nOf w) :
    𝒮.μ (𝒮.hasObservers ∩ {w | 𝒮.nOf w = 3 ∧ 𝒮.mOf w = 1}) = 𝒮.μ 𝒮.hasObservers := by
  sorry

end Tegmark
