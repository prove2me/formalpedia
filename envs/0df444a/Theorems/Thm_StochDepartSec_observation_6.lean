-- Prove2me | Theorems.Thm_StochDepartSec_observation_6
-- name    : StochDepartSec.observation_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:35.45699+00:00
-- url     : https://prove2.me/theorems/7edda926-ae45-4278-97d2-7f39bc246d89
-- title:
--   Observation 6 — without loss of optimality only best-so-far candidates are accepted
-- statement:
--   Throughout, $n$ is the number of candidates, $\mathcal A$ is an arrival distribution with $\mathcal A([0,1])=1$ and $\mathcal L$ a waiting time distribution with $\mathcal L([0,\infty))=1$; no other assumption (atoms, continuity) is made on $\mathcal A$ or $\mathcal L$.
--
--   **Observation 6.** For every admissible policy $\mathrm{pol}$ there is an admissible policy $\mathrm{pol}'$ that accepts a candidate only if that candidate is the best-so-far at its departure time, and
--
--   $$
--   \Pr[\mathrm{success}(\mathrm{pol})]\le\Pr[\mathrm{success}(\mathrm{pol}')].
--   $$
--
--   In particular an optimal policy can be taken to accept only best-so-far candidates, so the analysis of the optimal policy only needs to consider the times at which a best-so-far candidate departs.
--
--   Differences from the source:
--   - reading: opt only accepts candidates that are best-so-far → every admissible policy is weakly beaten by an admissible policy that accepts only best-so-far candidates; reason: opt is the paper's unique lazy optimal policy, an object the paper does not construct; the observation is used in this without-loss-of-optimality form (Lemma 9 considers only best-so-far departures), and the paper's form with opt optimal implies it
--   - encoding: candidates indexed by arrival order, overall order a permutation π with π(i) = 1 the best → fixed labels Fin n and a uniform permutation σ with σ i = 0 the best; reason: a relabelling; labels are independent of the times and the order, and ranks are shifted by one
--   - generalization: policies decide from the history (a, d, r) at time t → admissible policies may also read the candidates' labels and an independent uniform seed u ∈ [0,1]; reason: the comparison class is larger; the paper's deterministic policies are the members constant in u and symmetric in labels, and the bivariate policy belongs to the paper's class, so the Lean statement implies the paper's
--   - encoding: a policy → a policy whose acceptance events are measurable; reason: the success probability of a policy is only defined when its success event is measurable
--   - encoding: probabilities → ENNReal measures converted with toReal; reason: all values are in [0,1]
--   - encoding: the algorithm irrevocably accepts or rejects each departing candidate and hires one candidate → a policy names at most one candidate per instant (Option (Fin n)), a candidate is accepted iff named at its own departure time, and success means the earliest accepted candidate is the best overall; reason: only the first acceptance is a hire, so neither later acceptances nor the choice among simultaneous departures beyond one changes any outcome
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, Observation 6, p.7

import Mathlib
import Definitions.Def_StochDepartSec_Outcome
import Definitions.Def_StochDepartSec_dep
import Definitions.Def_StochDepartSec_BestSoFar
import Definitions.Def_StochDepartSec_Policy
import Definitions.Def_StochDepartSec_Policy_Admissible
import Definitions.Def_StochDepartSec_Policy_successProb
open MeasureTheory

namespace StochDepartSec

/-- Observation 6: without loss of optimality a policy accepts only best-so-far candidates. Every
admissible policy is weakly beaten by an admissible policy that accepts a candidate only if the
candidate is the best-so-far at its departure time.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, Observation 6, p.7: "opt only accepts candidates that are best-so-far."

The instance: `n` candidates, arrival distribution `A` with `A [0,1] = 1` ("events only occur in the interval [0, 1]", §2, p.5), waiting time distribution `L` with `L [0,∞) = 1` ("a non-negative real number", §2, p.5); no other assumption on `A` or `L` ("The results of Section 3 all hold for arbitrary arrival distributions except for Lemma 12", p.5).

**Formalization Note** The paper states the observation about the optimal lazy policy `opt`; this
is the "without loss of optimality" form the paper uses it in (Lemma 9's proof considers only
best-so-far departures). -/
theorem observation_6 {n : ℕ} (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] (hA : A (Set.Icc 0 1) = 1) (hL : L (Set.Ici 0) = 1)
    (pol : Policy n) (hpol : pol.Admissible) :
    ∃ pol' : Policy n, pol'.Admissible ∧
      (∀ (ω : Outcome n) (i : Fin n), pol'.Accepts ω i → BestSoFar ω (dep ω i) i) ∧
      pol.successProb A L ≤ pol'.successProb A L := by sorry

end StochDepartSec
