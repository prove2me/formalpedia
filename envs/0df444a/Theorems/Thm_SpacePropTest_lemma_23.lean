-- Prove2me | Theorems.Thm_SpacePropTest_lemma_23
-- name    : SpacePropTest.lemma_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:23.328568+00:00
-- url     : https://prove2.me/theorems/2886cb07-9265-4f4c-8ce5-0303ae9356c4
-- title:
--   Lemma 23, p.19 — the noisy version $f_\rho=T_\rho f$: monotone if $f$ is, many violated edges if $f$ is far, Fourier weight above level $L$ at most $O(\varepsilon^6/n^6)$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n\ge1$, $\varepsilon\in(0,1]$, $\rho=1-\varepsilon^2/(128\sqrt n)$, and $L\ge1$ an integer with $\rho\le1-3\ln(n/\varepsilon)/L$ as in (5). For every $f:\{\pm1\}^n\to\{\pm1\}$, with $f_\rho=T_\rho f$:
--
--   1. if $f$ is monotone, then $f_\rho$ is monotone and $\Pr_{x,i}[D_if_\rho(x)<0]=0$;
--   2. if $f$ is $\varepsilon$-far from monotone and $\mathrm{NS}_{(1-\rho)/2}[f]\le\varepsilon^2/128$, then
--   $$\Pr_{x\sim\{\pm1\}^n,\,i\sim[n]}\Big[D_if_\rho(x)\le-\frac{3}{4n}\Big]\ge\frac{\varepsilon}{n^3};$$
--   3. $f_\rho$ is $\alpha$-concentrated on levels up to $L$ with $\alpha=C\varepsilon^6/n^6$:
--   $$\sum_{S:\,|S|\ge L}\hat f_\rho(S)^2\le C\,\frac{\varepsilon^6}{n^6}.$$
--
--   Noise preserves monotonicity and violations of monotonicity while pushing the Fourier spectrum onto low levels, which the truncation of Lemma 24 exploits.
--
--   Differences from the source:
--   - encoding: $f:\{\pm1\}^n\to\{\pm1\}$ on $\{\pm1\}^n$ → a Boolean function on $\{0,1\}^n$ (`Fin n → Bool`) read through $\mathrm{false}\mapsto-1$, $\mathrm{true}\mapsto+1$; reason: order-preserving bijection; the same monotone functions, derivatives and Fourier coefficients
--   - encoding: $\Pr_{x\sim\{\pm1\}^n,\,i\sim[n]}[\cdot]$ → the fraction of pairs $(x,i)\in\{0,1\}^n\times[n]$ satisfying the event; reason: $x$ and $i$ are uniform and independent
--   - reading: $\rho=1-\Theta(\log(n/\varepsilon)/L)$ as in (5) → $\rho=1-\varepsilon^2/(128\sqrt n)$ exactly, $n\ge1$, $\varepsilon\in(0,1]$; reason: (5) sets $\rho$ by this formula; the $\Theta$ only records its relation to $L$
--   - generalization: $L:=O(\sqrt n\log(n/\varepsilon)/\varepsilon^2)$ such that $\rho\le1-3\log(n/\varepsilon)/L$ (5) → every positive integer $L$ with $\rho\le1-3\ln(n/\varepsilon)/L$; reason: every $L$ the paper allows satisfies this condition, so the statement specializes to the paper's $L$
--   - reading: “$f_\rho$ has Fourier spectrum $\alpha$-concentrated on levels up to $L$, for $\alpha=O(\varepsilon^6/n^6)$” → $\sum_{|S|\ge L}\hat f_\rho(S)^2\le C\varepsilon^6/n^6$ with an absolute $C$ chosen before $n,\varepsilon,L,f$; reason: Fact 19 (p.19) defines $\alpha$-concentration on levels up to $k$ by the weight on $|S|\ge k$; the standard reading of $O(\cdot)$
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Lemma 23, p.19 (PDF 21)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_Fourier

set_option autoImplicit false

namespace SpacePropTest

/-- **Lemma 23** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space Complexity
of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.19 (PDF 21)). With `ρ, L`
as in (5) and `f_ρ := T_ρ f`, for every `f : {±1}ⁿ → {±1}`:
1. if `f` is monotone, so is `f_ρ`, and `Pr_{x,i}[D_i f_ρ(x) < 0] = 0`;
2. if `f` is `ε`-far from monotone and `NS_{(1−ρ)/2}[f] ≤ ε²/128`, then
   `Pr_{x,i}[D_i f_ρ(x) ≤ −3/(4n)] ≥ ε/n³`;
3. `f_ρ` is `α`-concentrated on levels up to `L` for `α = O(ε⁶/n⁶)`:
   `∑_{|S| ≥ L} f̂_ρ(S)² ≤ C ε⁶/n⁶` with `C` absolute.

**Formalization Note.** `C` is chosen before `n, ε, L, f`. "α-concentrated on levels up to `L`"
is read as in Fact 19 (p.19): the Fourier weight on levels `|S| ≥ L` is at most `α`. -/
theorem lemma_23 : ∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (L : ℕ),
    IsLParam n ε L → ∀ f : BoolFn n,
      (f ∈ Mon n → Monotone (noiseOp (rho n ε) (pmFn f)) ∧
          edgeProbLt (noiseOp (rho n ε) (pmFn f)) 0 = 0) ∧
      (IsFar (Mon n) f ε → noiseSens ((1 - rho n ε) / 2) f ≤ ε ^ 2 / 128 →
          ε / (n : ℝ) ^ 3 ≤ edgeProbLe (noiseOp (rho n ε) (pmFn f)) (-3 / (4 * n))) ∧
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => L ≤ S.card),
          fourier (noiseOp (rho n ε) (pmFn f)) S ^ 2 ≤ C * ε ^ 6 / (n : ℝ) ^ 6) := by sorry

end SpacePropTest
