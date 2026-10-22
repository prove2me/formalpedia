-- Prove2me | Theorems.Thm_UnknownProphet_NoSamples_theorem_2
-- name    : UnknownProphet.NoSamples.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:54.414713+00:00
-- url     : https://prove2.me/theorems/698f7219-f098-443e-ae3a-bdcd7b79f658
-- title:
--   Theorem 2, p. 6 — no zero-sample rule guarantees above $1/e$
-- statement:
--   For every $\delta>0$ there is a horizon threshold $n_0$ such that, for every $n\ge n_0$ and every zero-sample stopping rule $r$, a nonnegative distribution $F$ can be chosen after $r$ so that the prophet's expected maximum is positive and
--
--   $$
--   \mathbb E_F[X_\tau]\le(e^{-1}+\delta)\,\mathbb E_F\!\left[\max_{1\le i\le n}X_i\right],
--   \qquad \mathbb E_F\!\left[\max_{1\le i\le n}X_i\right]>0.
--   $$
--
--   Thus no rule without samples can guarantee a ratio strictly above $1/e$ uniformly over the common law.
--
--   **Formalization Note** The law is finitely supported, matching the hard instance constructed in the proof. Positivity of the benchmark excludes the zero point mass, which would otherwise make the printed existential inequality vacuous. Indices are zero-based in Lean, and failure to stop yields payoff zero.
-- source:
--   Correa, Dütting, Fischer & Schewior, Prophet Inequalities for I.I.D. Random Variables from an Unknown Distribution, arXiv:1811.06114v2, p. 6, Theorem 2

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model

namespace UnknownProphet.NoSamples

/-- Theorem 2, p. 6: every zero-sample rule has a positive-benchmark
finitely supported adversarial law on which its ratio is asymptotically at most `1/e`. -/
theorem theorem_2 (δ : ℝ) (hδ : 0 < δ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ R : StoppingRule 0 n,
      ∃ F : FinDist, 0 < expMax F n ∧
        expStop F R ≤ (Real.exp (-1) + δ) * expMax F n := by sorry

end UnknownProphet.NoSamples
