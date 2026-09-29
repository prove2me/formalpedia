-- Prove2me | Theorems.Thm_QFS_exists_whitneyBallData
-- name    : QFS.exists_whitneyBallData
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-09-06T18:33:40.080721+00:00
-- url     : https://prove2.me/theorems/587f4ed1-3527-403f-942b-323e860bca80
-- title:
--   Lemma A.1's quoted input: a Whitney ball family with Dyda's inequality
-- statement:
--   **An input Lemma A.1 quotes rather than proves — now an open target.**
--
--   For a ball $B = B_R(x_0) \subseteq \mathbb{R}^d$ and $\kappa \ge 1$, this asserts the existence of a *Whitney ball family* for $B$: a countable family of balls $B_i = B(c_i, r_i)$ together with an overlap bound $M \ge 1$ and a constant $c_D > 0$ such that
--
--   1. each enlarged ball $B(c_i, \kappa r_i)$ lies inside $B$;
--   2. no point of $\mathbb{R}^d$ lies in more than $M$ of the enlarged balls;
--   3. **Dyda's inequality**: for every $f$,
--   $$c_D\,[f]^2_{H^{\alpha/2}(B)} \;\le\; \sum_i [f]^2_{H^{\alpha/2}(B_i)} .$$
--
--   Lemma A.1 of the source passes from an enlarged ball to the same ball using a Whitney decomposition and inequality (13) of Dyda, both **quoted from the literature rather than proved**. In this formalization they are carried as the structure `QFS.WhitneyBallData`, an explicit hypothesis of `QFS.formHs_le_form_of_ballComparability` and of `QFS.formHs_le_form_of_theoremOneOneBall`. Proving this theorem discharges that hypothesis and removes one of the two things standing between the development and an unconditional Theorem 1.1.
--
--   The case $\kappa = 1$ is already proved and is trivial — the one-element family consisting of $B$ itself works, with $M = 1$ and $c_D = 1$ (`QFS.whitneyBallData_one`). The content is entirely in $\kappa > 1$, where a genuine Whitney decomposition is required.
--
--   **Formalization Note** The family is indexed by an arbitrary countable type carried in the structure, and the centres and radii are functions of the ball $(x_0, R)$, so a single `WhitneyBallData` supplies a decomposition for *every* ball at once, uniformly in the centre and radius. The seminorms are lower Lebesgue integrals valued in $[0,\infty]$, so no finiteness is asserted anywhere.
-- source:
--   https://github.com/dbenbenn/quadratic-forms-sobolev/blob/7a1a680db2124d46ce370c91fd450aa454edf491/QuadraticFormsSobolev/AppendixA.lean#L134-L159

import Definitions.Def_QFS_AppendixA
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric MeasureTheory ENNReal

theorem QFS.exists_whitneyBallData (d : ℕ) (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα2 : α < 2)
    (κ : ℝ) (hκ : 1 ≤ κ) : Nonempty (QFS.WhitneyBallData d α κ) := by sorry
