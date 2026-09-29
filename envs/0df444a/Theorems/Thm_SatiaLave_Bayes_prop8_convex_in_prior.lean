-- Prove2me | Theorems.Thm_SatiaLave_Bayes_prop8_convex_in_prior
-- name    : SatiaLave.Bayes.prop8_convex_in_prior
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:43:51.981089+00:00
-- url     : https://prove2.me/theorems/1df841b1-5fad-4d0f-b14b-b6b48ecce6c4
-- title:
--   Proposition 8 — the Bayesian optimal return f(i, g) is convex in the prior g
-- statement:
--   Let $f(i,g)$ be a bounded solution of the Bayesian recursive equations (10) of Satia and Lave (by Proposition 6 it is the unique one, the Bayesian optimal total expected discounted return). Let $g_1, g_2$ be priors on the unknown transition matrix and $0 \le t \le 1$.
--
--   **Proposition 8.** $f(i, g)$ is convex in $g$ for any state $i$:
--   $$
--   f\big(i,\ t\, g_1 + (1-t)\, g_2\big) \le t\, f(i, g_1) + (1-t)\, f(i, g_2).
--   $$
--
--   Convexity in the prior is what allows Jensen's inequality in the proof of Proposition 9.
--
--   **Formalization Note** The set of priors has no vector structure other than mixtures, so "convex in $g$" is read as convexity along mixtures $t g_1 + (1-t) g_2$ of priors (measures). The proof is in Satia's thesis (reference 14 of the paper).
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 735, Proposition 8

import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- Proposition 8: the Bayesian optimal return `f(i, g)` is convex in the prior `g`, along
mixtures `t g₁ + (1 - t) g₂` of priors. -/
theorem prop8_convex_in_prior {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f) (hb : IsBoundedOnPriors f)
    (g₁ g₂ : Measure (Mat S D)) (hg₁ : IsPrior g₁) (hg₂ : IsPrior g₂)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (i : S) :
    f i (ENNReal.ofReal t • g₁ + ENNReal.ofReal (1 - t) • g₂) ≤
      t * f i g₁ + (1 - t) * f i g₂ := by sorry

end SatiaLave.Bayes
