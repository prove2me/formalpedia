-- Prove2me | Theorems.Thm_TopDownParity1043_Main_corollary_1
-- name    : TopDownParity1043.Main.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:20:14.271232+00:00
-- url     : https://prove2.me/theorems/c3f78ba8-6eb9-4f43-8d69-04a56e94092b
-- title:
--   Corollary 1 — concavity, monotonicity and normalization
-- statement:
--   Let $f,g,h:\{0,1\}^V\to\mathbb R_{\ge0}$. The harmonic coefficients satisfy all three properties:
--
--   1. If $0\le\lambda\le1$ and $f=\lambda g+(1-\lambda)h$ pointwise, then
--   $$H_f(R)\ge\lambda H_g(R)+(1-\lambda)H_h(R)\quad\text{for every }R.$$
--   2. If $R\subseteq S$, then $H_f(R)\ge H_f(S)$.
--   3. For every $R$, $H_f(R)\le\mathbb E f=H_f(\varnothing)$.
--
--   These properties control the level sets and normalization of the harmonic coefficients. No positivity or normalization assumption on $f,g,h$ is imposed.
--
--   Differences from the source:
--   - encoding: coordinates [n] → an arbitrary finite type V with Boolean words V → Bool; reason: every finite coordinate set is equivalent to Fin |V|, including every subcube coordinate subtype
--   - encoding: finite nonnegative harmonic coefficients → values in ℝ≥0∞; reason: these coefficients are always finite, and extended inverses implement exactly the printed conventions at zero
--   - encoding: λ ∈ [0,1] → λ : ℝ≥0 with λ ≤ 1; reason: nonnegativity is in the type; under λ ≤ 1 the nonnegative subtraction 1-λ agrees with real subtraction
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Corollary 1, p. 17

import Mathlib
import Definitions.Def_TopDownParity1043_Main_HarmonicMean

set_option autoImplicit false
open scoped NNReal ENNReal

namespace TopDownParity1043.Main

/-- Corollary 1, p.17: all three numbered parts, including the equality at the
empty set in part 3. All functions may take the value zero. -/
theorem corollary_1 (V : Type) [Fintype V] [DecidableEq V]
    (f g h : (V → Bool) → ℝ≥0) :
    (∀ lam : ℝ≥0, lam ≤ 1 → (∀ x, f x = lam * g x + (1 - lam) * h x) →
      ∀ R : Finset V, (lam : ℝ≥0∞) * harmonicMean g R +
        ((1 - lam : ℝ≥0) : ℝ≥0∞) * harmonicMean h R ≤ harmonicMean f R) ∧
    (∀ R S : Finset V, R ⊆ S → harmonicMean f S ≤ harmonicMean f R) ∧
    (∀ R : Finset V, harmonicMean f R ≤ (cubeMean f : ℝ≥0∞)) ∧
    (cubeMean f : ℝ≥0∞) = harmonicMean f ∅ := by sorry

end TopDownParity1043.Main
