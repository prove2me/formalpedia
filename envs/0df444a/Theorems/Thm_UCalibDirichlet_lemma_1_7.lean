-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_1_7
-- name    : UCalibDirichlet.lemma_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:57.674222+00:00
-- url     : https://prove2.me/theorems/2d6541e7-0090-4e6d-a9ca-34f781eb0da0
-- title:
--   Lemma 1.7 — $\mathrm{Cov}(f'(X),X)\le C_0\sup_x\{B_nf(x)-f(x)\}$
-- statement:
--   There is a universal constant $C_0$ such that for all integers $a,m\ge1$, with $n=a+m$, every continuous convex $f:[0,1]\to\mathbb R$ and $X\sim\mathrm{Beta}(a,m)$,
--   $$\mathrm{Cov}\big(f'(X),X\big)\le C_0\sup_{x\in[0,1]}\big\{B_nf(x)-f(x)\big\}.$$
--
--   Together with Lemma 1.6 it bounds each stability term by a scalar Bernstein approximation gap.
--
--   Differences from the source:
--   - encoding: Cov(f′(X), X) with X ∼ Beta(a, m) → bregCov f a m = ½E[(f′(X) − f′(Y))(X − Y)] ∈ [0, +∞], f′ = deriv f; reason: the paper's equivalent form (12); equal to the covariance when it is finite; the statement also asserts finiteness
--   - encoding: a universal constant C₀ → ∃ C₀ : ℝ before a, m and f; reason: universal = independent of a, m and f
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 1.7, display (13), p.5

import Mathlib
import Definitions.Def_UCalibDirichlet_bern
import Definitions.Def_UCalibDirichlet_bregCov

namespace UCalibDirichlet

/-- **Lemma 1.7 (scalar Bernstein window).** Frongillo, Luo, Mehta & Schneider (manuscript, STOC
2027 submission), Lemma 1.7, display (13), p.5: "Let `a, m ≥ 1` and `n = a + m` be integers. If
`f : [0, 1] → ℝ` is continuous and convex and `X ∼ Beta(a, m)`, then for a universal constant `C₀`,
`Cov(f′(X), X) ≤ C₀ sup_{x∈[0,1]} {B_n f(x) − f(x)}`. (13)"

**Formalization Note.** `C₀` is one `∃` before `a`, `m` and `f`. `Cov(f′(X), X)` is `bregCov f a m`,
the symmetric form `½ E[(f′(X) − f′(Y))(X − Y)]` (display (12)), valued in `[0, +∞]`; the statement
therefore also asserts that the covariance is finite. The right side is nonnegative
(`B_n f(0) = f(0)`), so `ENNReal.ofReal` loses nothing. `f′ = deriv f`. -/
theorem lemma_1_7 : ∃ C₀ : ℝ, ∀ a m : ℕ, 1 ≤ a → 1 ≤ m → ∀ f : ℝ → ℝ,
    ContinuousOn f (Set.Icc 0 1) → ConvexOn ℝ (Set.Icc 0 1) f →
      bregCov f a m ≤ ENNReal.ofReal (C₀ * ⨆ x : Set.Icc (0 : ℝ) 1, (bern f (a + m) x - f x)) := by sorry

end UCalibDirichlet
