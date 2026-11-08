-- Prove2me | Theorems.Thm_ProperHalfspace_lemma_24
-- name    : ProperHalfspace.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:53.490063+00:00
-- url     : https://prove2.me/theorems/4bc32b7f-9fb0-4d16-bfb0-434f0cf389ac
-- title:
--   Lemma 24 — decay of $D(t,s)$
-- statement:
--   Let $\|w\|_2=1$, $\beta_w=(\sum_iw_i^4)^{1/2}$ and $T=\beta_w^{-1/2}$. With $R_t$ and $D(t,s)=\mathbf E_{z\sim N(0,I_n)}[R_t(z)\overline{R_s(z)}]$ as in (33), there is a universal constant $C$ such that for $|t|,|s|\le T$,
--   $$|D(t,s)|\le C\beta_w^2\,|ts|\,(|t|+|s|)^2e^{-(t-s)^2/4}.$$
--
--   The decay in $t-s$ is what is used when integrating over the frequencies in the proof of Proposition 7.
--
--   Differences from the source:
--   - encoding: the standing setting of §A (‖w‖₂ = 1, β_w, T, R_t), stated before the lemma → binders of the theorem, with C before n and w; reason: C is universal, as on p.10
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Lemma 24, (34), p.40

import Mathlib
import Definitions.Def_ProperHalfspace_ExpComparison

namespace ProperHalfspace

/-- Lemma 24, (34), p.40. De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026).
With `‖w‖₂ = 1`, `β_w = (Σ wᵢ⁴)^{1/2}` and `T = β_w^{−1/2}`: for `|t|, |s| ≤ T`,
`|D(t, s)| ≤ C β_w² |t s| (|t| + |s|)² e^{−(t−s)²/4}`, with `C` universal. -/
theorem lemma_24 : ∃ C : ℝ, ∀ (n : ℕ) (w : Fin n → ℝ), ∑ i, w i ^ 2 = 1 → ∀ t s : ℝ,
    |t| ≤ betaW w ^ (-(1 / 2) : ℝ) → |s| ≤ betaW w ^ (-(1 / 2) : ℝ) →
    ‖expCorr w t s‖ ≤ C * betaW w ^ 2 * |t * s| * (|t| + |s|) ^ 2 * Real.exp (-(t - s) ^ 2 / 4) := by sorry

end ProperHalfspace
