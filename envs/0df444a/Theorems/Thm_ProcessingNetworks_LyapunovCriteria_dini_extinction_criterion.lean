-- Prove2me | Theorems.Thm_ProcessingNetworks_LyapunovCriteria_dini_extinction_criterion
-- name    : ProcessingNetworks.LyapunovCriteria.dini_extinction_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T18:00:49.742019+00:00
-- url     : https://prove2.me/theorems/97d8b441-3b1a-4ac7-9e24-9bfe10e7b886
-- title:
--   Lemma 8.11 — general Dini-derivative extinction criterion (goal)
-- statement:
--   This is the goal theorem of the mission: the general-purpose extinction criterion that Lemmas
--   8.5 and 8.6 both specialize, stated for a bare function with no reference to a fluid model at
--   all — pure real analysis, reusable by any later mission (in particular, the non-Lipschitz
--   entropy Lyapunov function of missions IX/X) exactly as stated here.
--
--   **Lemma 8.11.** Assume $f : \mathbb{R}_+ \to \mathbb{R}_+$ satisfies: (a) $f$ is continuous
--   on $(0,\infty)$; (b) for each interval $[a,b) \subset \mathbb{R}_+$ there is $M > 0$ with
--   $D^+f(t) \le M$ for all $t \in [a,b)$; (c) there is $\varepsilon > 0$ such that
--   $D^+f(t) \le -\varepsilon$ for almost every $t \in \mathbb{R}_+$ with $f(t) > 0$. Then
--   $f(t) = 0$ for $t \ge f(0)/\varepsilon$.
--
--   Unlike Lemma 8.5, $f$ need not be Lipschitz here — only continuous with a *locally* bounded
--   upper Dini derivative — which is exactly what lets this criterion apply to Lyapunov functions
--   that are not everywhere differentiable or Lipschitz (e.g. Chapter 10's entropy function).
--
--   **Formalization note.** $D^+f$ (`diniUpperRight`) is used throughout, not `deriv f` — using
--   the ordinary derivative would be a strictly stronger (hence unfaithful) hypothesis, since
--   $D^+f(t)$ is defined at every $t$ while `deriv f t` presupposes differentiability. The Dini
--   derivative takes values in the extended reals, so that condition (b), $D^+f(t) \le M$ on
--   $[a,b)$, genuinely excludes points where $D^+f(t) = +\infty$ (with a real-valued junk
--   convention the bound would hold vacuously there, and a Cantor-type function with $D^+f = +\infty$
--   on a null set would refute the lemma), and condition (c) is satisfied at points where
--   $D^+f(t) = -\infty$, as it should be. Condition (b)'s bound $M$ is stated as `0 < M` (the
--   book's own "there exists a constant $M > 0$"); the hypothesis and conclusion match (8.6)-(8.7)
--   and the final claim exactly, with no fluid-model machinery smuggled in, per this mission's own
--   `BRIEF.md` warning to keep the statement generic.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 139, Lemma 8.11

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative

namespace ProcessingNetworks.LyapunovCriteria

open MeasureTheory

/-- Lemma 8.11, Dai & Harrison p. 139 (PDF p. 155) — the goal theorem of this mission: assume
`f : ℝ_+ → ℝ_+` satisfies (a) `f` is continuous on `(0,∞)`; (b) for each interval `[a,b) ⊂ ℝ_+`
there is `M > 0` with `D⁺f(t) ≤ M` for all `t ∈ [a,b)` (8.6); (c) there is `ε > 0` such that
`D⁺f(t) ≤ -ε` for almost all `t ∈ ℝ_+` with `f(t) > 0` (8.7). Then `f(t) = 0` for
`t ≥ f(0)/ε`. This generalizes Lemma 8.5 to Lyapunov functions `H` that are merely continuous,
not Lipschitz. -/
theorem dini_extinction_criterion
    (f : ℝ → ℝ) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Set.Ico a b, diniUpperRight f t ≤ (M : EReal))
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → diniUpperRight f t ≤ ((-ε : ℝ) : EReal)) :
    ∀ t : ℝ, f 0 / ε ≤ t → f t = 0 := by sorry

end ProcessingNetworks.LyapunovCriteria
