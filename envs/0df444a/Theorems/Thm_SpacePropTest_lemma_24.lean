-- Prove2me | Theorems.Thm_SpacePropTest_lemma_24
-- name    : SpacePropTest.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:28.120528+00:00
-- url     : https://prove2.me/theorems/a67ce1a3-4ad4-4ace-ac90-548b1202dc29
-- title:
--   Lemma 24, p.21 — the truncation $f_\rho^{\le L}$: few edges below $-1/(4n)$ if $f$ is monotone, at least $\varepsilon/(2n^3)$ below $-1/(2n)$ if $f$ is far
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n\ge1$, $\varepsilon\in(0,1]$, and $\rho,L$ as in (5). For every $f:\{\pm1\}^n\to\{\pm1\}$ the truncation $f_\rho^{\le L}$ of eq. (7) satisfies:
--
--   1. if $f$ is monotone, then $\Pr_{x,i}\big[D_if_\rho^{\le L}(x)\le-\tfrac1{4n}\big]\le\beta$ with $\beta=C\varepsilon^6/n^4$;
--   2. if $f$ is $\varepsilon$-far from monotone and $\mathrm{NS}_{(1-\rho)/2}[f]\le\varepsilon^2/128$, then
--   $$\Pr_{x\sim\{\pm1\}^n,\,i\sim[n]}\Big[D_if_\rho^{\le L}(x)\le-\frac1{2n}\Big]\ge\frac{\varepsilon}{2n^3}.$$
--
--   The degree-$L$ polynomial $f_\rho^{\le L}$ thus separates monotone from far functions through the sign statistics of its derivatives.
--
--   Differences from the source:
--   - encoding: $f:\{\pm1\}^n\to\{\pm1\}$ on $\{\pm1\}^n$ → a Boolean function on $\{0,1\}^n$ (`Fin n → Bool`) read through $\mathrm{false}\mapsto-1$, $\mathrm{true}\mapsto+1$; reason: order-preserving bijection; the same monotone functions, derivatives and Fourier coefficients
--   - encoding: $\Pr_{x\sim\{\pm1\}^n,\,i\sim[n]}[\cdot]$ → the fraction of pairs $(x,i)\in\{0,1\}^n\times[n]$ satisfying the event; reason: $x$ and $i$ are uniform and independent
--   - reading: $\rho=1-\Theta(\log(n/\varepsilon)/L)$ as in (5) → $\rho=1-\varepsilon^2/(128\sqrt n)$ exactly, $n\ge1$, $\varepsilon\in(0,1]$; reason: (5) sets $\rho$ by this formula; the $\Theta$ only records its relation to $L$
--   - generalization: $L:=O(\sqrt n\log(n/\varepsilon)/\varepsilon^2)$ such that $\rho\le1-3\log(n/\varepsilon)/L$ (5) → every positive integer $L$ with $\rho\le1-3\ln(n/\varepsilon)/L$; reason: every $L$ the paper allows satisfies this condition, so the statement specializes to the paper's $L$
--   - encoding: “for some $\beta=O(\varepsilon^6/n^4)$” → $\beta=C\varepsilon^6/n^4$ with an absolute $C$ chosen before $n,\varepsilon,L,f$; reason: standard reading of $O(\cdot)$
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Lemma 24, p.21 (PDF 23)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_Fourier

set_option autoImplicit false

namespace SpacePropTest

/-- **Lemma 24** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space Complexity
of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.21 (PDF 23)). With `ρ, L`
as in (5), for every `f : {±1}ⁿ → {±1}` the truncation `f_ρ^{≤L}` of eq. (7) satisfies:
1. if `f` is monotone, `Pr_{x,i}[D_i f_ρ^{≤L}(x) ≤ −1/(4n)] ≤ β` for some `β = O(ε⁶/n⁴)`;
2. if `f` is `ε`-far from monotone and `NS_{(1−ρ)/2}[f] ≤ ε²/128`, then
   `Pr_{x,i}[D_i f_ρ^{≤L}(x) ≤ −1/(2n)] ≥ ε/(2n³)`.

**Formalization Note.** `β = O(ε⁶/n⁴)` is `β ≤ C ε⁶/n⁴` with `C` absolute, chosen before
`n, ε, L, f`. Item 2 is stated for all `n ≥ 1`, as printed. -/
theorem lemma_24 : ∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (L : ℕ),
    IsLParam n ε L → ∀ f : BoolFn n,
      (f ∈ Mon n →
          edgeProbLe (trunc L (noiseOp (rho n ε) (pmFn f))) (-1 / (4 * n)) ≤
            C * ε ^ 6 / (n : ℝ) ^ 4) ∧
      (IsFar (Mon n) f ε → noiseSens ((1 - rho n ε) / 2) f ≤ ε ^ 2 / 128 →
          ε / (2 * (n : ℝ) ^ 3) ≤
            edgeProbLe (trunc L (noiseOp (rho n ε) (pmFn f))) (-1 / (2 * n))) := by sorry

end SpacePropTest
