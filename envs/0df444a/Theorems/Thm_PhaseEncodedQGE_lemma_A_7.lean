-- Prove2me | Theorems.Thm_PhaseEncodedQGE_lemma_A_7
-- name    : PhaseEncodedQGE.lemma_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:42.973451+00:00
-- url     : https://prove2.me/theorems/ba480ff9-5dbe-4cfc-9d20-e5030198449e
-- title:
--   Lemma A.7 — $\tan^2(\eta/2)$ is transcendental for nonzero algebraic $\eta$; the schedule
-- statement:
--   Let $\eta$ be a nonzero real algebraic number with $\cos\eta\ne-1$. Then $t^2=\tan^2(\eta/2)$ is transcendental over $\mathbb Q$. At the schedule:
--
--   1. $\eta=23/8$, so $\tan^2(23/16)$ is transcendental and in particular irrational;
--   2. $\gamma=2$ is not in $(\pi/2)\mathbb Z$, so $h_e\ne h_o$ for $r=1$, i.e. $h^{X,1}(0)\ne h^{X,1}(1)$ at $\gamma=2$.
--
--   This supplies hypothesis (b) of Theorem A.8 at the schedule for every $n$.
--
--   Differences from the source:
--   - reading: $\eta$ a nonzero algebraic number → $\eta\in\mathbb R$, $\eta\ne0$, algebraic over $\mathbb Q$; reason: η is a preparation angle, a real number throughout the paper
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.2, p.15 (PDF p.16), Lemma A.7

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Profile
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Lemma A.7, transcendence of the layer ratio (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. A.1.2, p.15).

Let `η` be a nonzero algebraic number with `cos η ≠ −1`. Then `t² = tan²(η/2)` is transcendental.
At the schedule, `η = 23/8`, so `t²` is transcendental and in particular irrational; and `γ = 2` is
not in `(π/2)ℤ`, so `h_e ≠ h_o` for `r = 1`.

**Formalization Note** `η` is real and "algebraic" is `IsAlgebraic ℚ η`; transcendence is over `ℚ`.
`h_e = h^{X,1}(0)` and `h_o = h^{X,1}(1)` at `γ = 2`. -/
theorem lemma_A_7 :
    (∀ η : ℝ, η ≠ 0 → IsAlgebraic ℚ η → Real.cos η ≠ -1 →
      Transcendental ℚ (Real.tan (η / 2) ^ 2)) ∧
    Transcendental ℚ (Real.tan ((23 / 8 : ℝ) / 2) ^ 2) ∧
    Irrational (Real.tan ((23 / 8 : ℝ) / 2) ^ 2) ∧
    (¬ ∃ k : ℤ, (2 : ℝ) = Real.pi / 2 * k) ∧
    hX 1 2 0 ≠ hX 1 2 1 := by sorry

end PhaseEncodedQGE
