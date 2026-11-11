-- Prove2me | Theorems.Thm_SpacePropTest_lemma_22
-- name    : SpacePropTest.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:33.79469+00:00
-- url     : https://prove2.me/theorems/35ae1db5-ef14-4847-89fb-b70b55825421
-- title:
--   Lemma 22, p.19 — monotone functions have $\mathrm{NS}_{(1-\rho)/2}[f]\le\varepsilon^2/256$
-- statement:
--   Let $n\ge1$, $\varepsilon\in(0,1]$ and $\rho=1-\varepsilon^2/(128\sqrt n)$ as in (5). Every monotone $f:\{\pm1\}^n\to\{\pm1\}$ satisfies
--
--   $$\mathrm{NS}_{\frac{1-\rho}{2}}[f]\le\frac{\varepsilon^2}{256}.$$
--
--   This is the completeness half of the noise-sensitivity test of the monotonicity tester.
--
--   Differences from the source:
--   - encoding: $f:\{\pm1\}^n\to\{\pm1\}$ on $\{\pm1\}^n$ → a Boolean function on $\{0,1\}^n$ (`Fin n → Bool`) read through $\mathrm{false}\mapsto-1$, $\mathrm{true}\mapsto+1$; reason: order-preserving bijection; the same monotone functions, derivatives and Fourier coefficients
--   - reading: $\rho=1-\Theta(\log(n/\varepsilon)/L)$ as in (5) → $\rho=1-\varepsilon^2/(128\sqrt n)$ exactly, $n\ge1$, $\varepsilon\in(0,1]$; reason: (5) sets $\rho$ by this formula; the $\Theta$ only records its relation to $L$
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Lemma 22, p.19 (PDF 21)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_Fourier

set_option autoImplicit false

namespace SpacePropTest

/-- **Lemma 22 (Monotone functions have low sensitivity)** (C. Canonne, X. Chen, W. Pires,
T. Pitassi, R. A. Servedio, *The Space Complexity of Property Testing*, manuscript of November 2,
2026, sha256 65850aa6…; p.19 (PDF 21)). With `ρ = 1 − ε²/(128√n)` as in (5), every monotone
`f : {±1}ⁿ → {±1}` has `NS_{(1−ρ)/2}[f] ≤ ε²/256`.

**Formalization Note.** `n ≥ 1`, `ε ∈ (0, 1]`; `ρ` is `rho n ε` of eq. (5); `f` is read through the
order-preserving `±1` encoding. -/
theorem lemma_22 (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (f : BoolFn n)
    (hf : f ∈ Mon n) :
    noiseSens ((1 - rho n ε) / 2) f ≤ ε ^ 2 / 256 := by sorry

end SpacePropTest
