-- Prove2me | Theorems.Thm_RobustQSC_Supplement_theorem_2
-- name    : RobustQSC.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:11:13.038217+00:00
-- url     : https://prove2.me/theorems/b1a2f018-748c-4ad9-b290-c3a192fcc0f0
-- title:
--   Theorem 2 — uncertainty principle for weighted total influence: $\mathrm{Inf}_{\mu_f}[g/f]+\mathrm{Inf}_{\mu_{\hat f}}[\hat g/\hat f]\gtrsim n$
-- statement:
--   Let $f:\{0,1\}^n\to\mathbb C$ be Haar-random with $\|f\|_2=1$, and let $\hat f$ be its Fourier transform with the unitary normalization, $\hat f(s)=2^{-n/2}\sum_x f(x)(-1)^{s\cdot x}$. Write $\mu_f(x)=|f(x)|^2$ and $\mu_{\hat f}(s)=|\hat f(s)|^2$, and for a probability measure $\mu$ on $\{0,1\}^n$ and $h:\{0,1\}^n\to\mathbb C$ let
--   $$\mathrm{Inf}_\mu[h]=\sum_{i,x}\frac{2\mu(x)\mu(x+i)}{\mu(x)+\mu(x+i)}\Big|\frac{h(x)-h(x+i)}{2}\Big|^2$$
--   be the $\mu$-weighted total influence, where $x+i$ is $x$ with its $i$-th bit flipped.
--
--   There are universal constants $c>0$ and $c_0>0$ and an $n_0$ such that for every $n\ge n_0$, with probability at least $1-2^{-c_0 n}$ over $f$, every $g:\{0,1\}^n\to\mathbb C$ with $\|g\|_2=1$ and $\langle f,g\rangle=0$ satisfies
--   $$\mathrm{Inf}_{\mu_f}\Big[\frac gf\Big]+\mathrm{Inf}_{\mu_{\hat f}}\Big[\frac{\hat g}{\hat f}\Big]\ \ge\ c\,n.$$
--
--   This is the weighted form of the influence uncertainty principle; $\mathrm{Inf}_\mu$ is the Dirichlet energy of continuous-time Glauber dynamics with stationary law $\mu$. Via $\mathrm{Avg}_f[g]=1-\frac1n\mathrm{Inf}_{\mu_f}[g/f]$ it is equivalent to the uncertainty principle of Theorem 4, which drives the soundness of the certification protocol.
--
--   **Formalization Note** The probability is over the published Haar law `haarTargetLaw n` on unit vectors; the bad event is "some admissible $g$ violates the bound". The quotients are pointwise with $a/0=0$, which matters only on a Haar-null set.
--
--   Differences from the source:
--   - encoding: with probability 1 − 2^{−Ω(n)} over Haar-random f, for all admissible g, Inf_{µ_f}[g/f] + Inf_{µ_f̂}[ĝ/f̂] ≳ n → ∃ c > 0, ∃ c₀ > 0, ∃ n₀, ∀ n ≥ n₀: haarTargetLaw n {f | IsState f ∧ ∃ g, IsState g ∧ inner ℂ f g = 0 ∧ sum < c·n} ≤ 2^{−c₀ n}; reason: the paper defines A ≳ B as A ≥ cB for a universal c > 0 (p.8); 2^{−Ω(n)} is pinned as in the base mission's Theorem 4; the ∀ g sits inside the bad event
--   - encoding: the quotients g/f and ĝ/f̂ → pointwise quotients in ℂ with Lean's a/0 = 0; reason: f and f̂ vanish nowhere for Haar-almost every f, so the convention changes the event only on a null set
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Theorem 2, p.8 (Inf_µ and ≳ defined on p.8)

import Definitions.Def_RobustQSC_infMu
import Definitions.Def_QAlgorithms_Defs_HaarTargetStates

namespace RobustQSC.Supplement

open QAlgorithms QAlgorithms.TwoBasisCertification MeasureTheory RobustQSC

/-- **Theorem 2 (Uncertainty principle for weighted total influence).** With probability
`1 − 2^{−Ω(n)}` over a Haar-random `f : {0,1}ⁿ → ℂ` with `‖f‖₂ = 1`, for all `g : {0,1}ⁿ → ℂ`
with `‖g‖₂ = 1` and `⟨f, g⟩ = 0`, `Inf_{µ_f}[g/f] + Inf_{µ_f̂}[ĝ/f̂] ≳ n`, where
`µ_f(x) = |f(x)|²` and `µ_f̂(s) = |f̂(s)|²`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Theorem 2, p.8 (`Inf_µ` defined on p.8;
"`A ≳ B` means that there exists a universal constant `c > 0` such that `A ≥ cB`", p.8).

**Formalization Note.**
1. `≳ n` is `≥ c · n` for one universal `c > 0` chosen before `n` and `f`; "with probability
   `1 − 2^{−Ω(n)}`" is: for `n ≥ n₀`, the Haar measure (`haarTargetLaw`) of the set of unit `f`
   for which **some** admissible `g` violates the bound is at most `2^{−c₀ n}`.
2. `g/f` and `ĝ/f̂` are pointwise quotients; Lean's `a / 0 = 0` only matters where `f` or `f̂`
   vanishes, which happens on a Haar-null set.
3. `⟨f, g⟩ = Σ_x f̄(x) g(x)` is `inner ℂ f g`; `f̂ = fourier f` (unitary normalization). -/
theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      haarTargetLaw n {f | IsState f ∧ ∃ g : EuclideanSpace ℂ (Qubits n), IsState g ∧
          inner ℂ f g = 0 ∧
          infMu (muOf f) (fun x => g x / f x) +
              infMu (muOf (fourier f)) (fun s => fourier g s / fourier f s) < c * n}
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ * n))) := by sorry

end RobustQSC.Supplement
