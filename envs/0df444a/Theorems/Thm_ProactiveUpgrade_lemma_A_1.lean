-- Prove2me | Theorems.Thm_ProactiveUpgrade_lemma_A_1
-- name    : ProactiveUpgrade.lemma_A_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:52:21.658112+00:00
-- url     : https://prove2.me/theorems/6880c125-448a-4a82-851b-5e69d761d395
-- title:
--   Lemma A.1 — anti-multimodular iff $\Delta_a\Delta_b f\ge0$ on $\mathcal F$
-- statement:
--   A function $f$ on $\mathbb N^n$ is anti-multimodular if and only if
--
--   $$
--   \Delta_a\Delta_b f\ge0\qquad\text{for all } a,b\in\mathcal F,\ a\ne b,
--   $$
--
--   where the inequality is required at every point at which the second difference evaluates $f$ only on $\mathbb N^n$.
--
--   This is the second-difference characterization used throughout the proof of Proposition 4.
--
--   Differences from the source:
--   - reading: anti-multimodularity of f : ℤᵐ → ℝ, (A.1) for all x ∈ ℤᵐ (Definition A.1, p.31) → f on ℕᵐ, (A.1) whenever x, x + a, x + b, x + a + b all lie in ℕᵐ (AntiMultimodular); reason: the value functions are defined only for x ≥ 0 (p.10) and the proof of Proposition 4 treats exactly the quadrant (Case 1, p.37, excludes a, b ∈ {−e₁, d₂} at x₁ = x₂ = 0 because they leave it); this is Definition A.1 for the extension by −∞, the only extension the paper uses
--   - encoding: Δₐ for a ∈ 𝓕 and a ≠ b → Gen.toDir.delta with its shift (−e_{i−1} for d_i), a ≠ b as generators; reason: Lean convention; generator vectors are distinct, so a ≠ b as generators iff as vectors
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Lemma A.1, p.31

import Mathlib
import Definitions.Def_ProactiveUpgrade_Dir
import Definitions.Def_ProactiveUpgrade_Gen
import Definitions.Def_ProactiveUpgrade_AntiMultimodular

namespace ProactiveUpgrade

/-- **Lemma A.1** (Chen et al., SSRN 3777846, p.31). A function `f` is anti-multimodular iff
`∆_a ∆_b f ≥ 0` for all `a, b ∈ 𝓕` with `a ≠ b`.

**Formalization Note** On the quadrant: the second difference is required to be nonnegative at
every `x` whose four evaluation points lie in `ℕⁿ` (`EvalInQuad`), matching `AntiMultimodular`. -/
theorem lemma_A_1 {n : ℕ} (f : (Fin n → ℕ) → ℝ) :
    AntiMultimodular f ↔
      ∀ (a b : Gen n), a ≠ b → ∀ x : Fin n → ℤ, EvalInQuad a.toDir b.toDir x →
        0 ≤ a.toDir.delta (b.toDir.delta (liftZ f)) x := by sorry

end ProactiveUpgrade
