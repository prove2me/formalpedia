-- Prove2me | Theorems.Thm_SpacePropTest_lemma_27
-- name    : SpacePropTest.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:42.648629+00:00
-- url     : https://prove2.me/theorems/0ec57034-c36c-4d0d-967d-cbd16cd728dc
-- title:
--   Lemma 27, p.24 — a $2^{O(L\log(n/\varepsilon))}$-state clock-equipped estimator of $\mathrm{NS}_{(1-\rho)/2}[f]$ within $\varepsilon^2/512$ after $2^{O(L\log n)}/\varepsilon^4$ queries
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n\ge1$, $\varepsilon\in(0,1]$ and $\rho,L$ as in (5). There is a clock-equipped estimator with at most $2^{C L\log_2(2n/\varepsilon)}$ states that makes at most $2^{CL\log_2(2n)}/\varepsilon^4$ queries and, for every $f:\{\pm1\}^n\to\{\pm1\}$, outputs $\hat\gamma$ with
--
--   $$\Pr\Big[\big|\hat\gamma-\mathrm{NS}_{\frac{1-\rho}2}[f]\big|\le\frac{\varepsilon^2}{512}\Big]\ge\frac56.$$
--
--   This is the first of the two tests of the monotonicity tester.
--
--   Differences from the source:
--   - encoding: $f:\{\pm1\}^n\to\{\pm1\}$ on $\{\pm1\}^n$ → a Boolean function on $\{0,1\}^n$ (`Fin n → Bool`) read through $\mathrm{false}\mapsto-1$, $\mathrm{true}\mapsto+1$; reason: order-preserving bijection; the same monotone functions, derivatives and Fourier coefficients
--   - reading: $\rho=1-\Theta(\log(n/\varepsilon)/L)$ as in (5) → $\rho=1-\varepsilon^2/(128\sqrt n)$ exactly, $n\ge1$, $\varepsilon\in(0,1]$; reason: (5) sets $\rho$ by this formula; the $\Theta$ only records its relation to $L$
--   - generalization: $L:=O(\sqrt n\log(n/\varepsilon)/\varepsilon^2)$ such that $\rho\le1-3\log(n/\varepsilon)/L$ (5) → every positive integer $L$ with $\rho\le1-3\ln(n/\varepsilon)/L$; reason: every $L$ the paper allows satisfies this condition, so the statement specializes to the paper's $L$
--   - reading: clock-equipped algorithm (informal, pp.2–4, 17; formal definition deferred to [CCP+26]) → a $T$-step algorithm with time-indexed query and next-state distributions, a start state, and an output read off the state at time $T$; $S$ states means at most $S$ states, after $K$ queries means $T\le K$; reason: minimal reading of pp.2–4 and 17 (paper.md decision 6); the clock is not counted among the states, as in the paper's conversion to $O(ST)$ states
--   - encoding: $2^{O(L\log(n/\varepsilon))}$ states, $2^{O(L\log n)}/\varepsilon^4$ queries → at most $2^{CL\log_2(2n/\varepsilon)}$ states and $2^{CL\log_2(2n)}/\varepsilon^4$ queries, $C$ absolute and chosen before $n,\varepsilon,L$; the algorithm is chosen before $f$; reason: standard reading of $O(\cdot)$; $\log_2(2n)\ge1$ keeps the bound from collapsing at $n=1$ and equals $\log n$ up to the constant for $n\ge2$
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Lemma 27, p.24 (PDF 26)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_Fourier
import Definitions.Def_SpacePropTest_ClockAlg

set_option autoImplicit false

namespace SpacePropTest

/-- **Lemma 27 (Estimating the noise sensitivity)** (C. Canonne, X. Chen, W. Pires, T. Pitassi,
R. A. Servedio, *The Space Complexity of Property Testing*, manuscript of November 2, 2026,
sha256 65850aa6…; p.24 (PDF 26)). There is a `2^{O(L log(n/ε))}`-state clock-equipped algorithm
which, after `2^{O(L log n)}/ε⁴` queries, outputs `γ̂` with `|γ̂ − NS_{(1−ρ)/2}[f]| ≤ ε²/512`
with probability at least `5/6`, for every `f`.

**Formalization Note.** `C` is absolute and chosen before `n, ε, L`; the algorithm is chosen before
`f`. Inside the `O`-bounds, `log(n/ε)` is `log₂(2n/ε)` and `log n` is `log₂(2n)` (both `≥ 1`). -/
theorem lemma_27 : ∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (L : ℕ),
    IsLParam n ε L →
    ∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (E : ClockEstimator n σ),
      (Fintype.card σ : ℝ) ≤ 2 ^ (C * L * Real.logb 2 (2 * n / ε)) ∧
      (E.T : ℝ) ≤ 2 ^ (C * L * Real.logb 2 (2 * n)) / ε ^ 4 ∧
      ∀ f : BoolFn n,
        5 / 6 ≤ E.probWithin f (noiseSens ((1 - rho n ε) / 2) f - ε ^ 2 / 512)
          (noiseSens ((1 - rho n ε) / 2) f + ε ^ 2 / 512) := by sorry

end SpacePropTest
