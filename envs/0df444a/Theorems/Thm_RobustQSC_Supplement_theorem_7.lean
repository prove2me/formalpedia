-- Prove2me | Theorems.Thm_RobustQSC_Supplement_theorem_7
-- name    : RobustQSC.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:12:35.131186+00:00
-- url     : https://prove2.me/theorems/4dd416f2-5eec-4cc1-8a69-da51f4f30d15
-- title:
--   Theorem 7 — uncertainty principle for random phase states: $\mathrm{Avg}_f[g]+\mathrm{Avg}_{\hat f}[\hat g]\le 1.999$
-- statement:
--   A **random phase function** is $f:\{0,1\}^n\to\mathbb C$ with $f(x)=2^{-n/2}\omega_x$, where $(\omega_x)_x$ are independent uniform points of the unit circle; so $|f(x)|^2=2^{-n}$ for all $x$ and $\|f\|_2=1$. A function $g$ is **compatible** with $f$ if $\|g\|_2=1$ and $\langle f,g\rangle=0$. With $x+i$ the string $x$ with bit $i$ flipped, let
--   $$\mathrm{Avg}_f[g]=\frac1{2n}\sum_{i}\sum_x\frac{|\overline{f(x)}g(x)+\overline{f(x+i)}g(x+i)|^2}{|f(x)|^2+|f(x+i)|^2}.$$
--
--   There are $c_0>0$ and $n_0$ such that for every $n\ge n_0$, except with probability at most $2^{-c_0n}$ over $f$, every $g$ compatible with $f$ satisfies
--   $$\mathrm{Avg}_f[g]+\mathrm{Avg}_{\hat f}[\hat g]\ \le\ 1.999,$$
--   where $\hat f,\hat g$ are the unitary Walsh–Hadamard transforms.
--
--   This is the uncertainty principle of Theorem 4 in the special case of phase states, with the explicit constant $c=0.001$; the paper proves it as a warm-up for the general Haar case.
--
--   **Formalization Note** The law of $f$ is the published `phaseLaw (fun _ => 1 / 2^n)` (i.i.d. Steinhaus phases scaled by $\sqrt{2^{-n}}$); `avg` is the published $\mathrm{Avg}$. The bad event is "some compatible $g$ violates the bound".
--
--   Differences from the source:
--   - encoding: f a random phase function → f ∼ phaseLaw (fun _ => 1/2^n), i.e. f(x) = 2^{−n/2}ω_x with (ω_x) i.i.d. Steinhaus; reason: phase states are |f(x)|² = 2^{−n} (p.12) with uniformly random phases; the proof (pp.45–46) works with µ = unif and f ∼ F_µ, which is the published phaseLaw
--   - encoding: for n large enough … except with probability 2^{−Ω(n)} over the choice of f → ∃ c₀ > 0, ∃ n₀, ∀ n ≥ n₀: phaseLaw {f | ∃ g, IsState g ∧ inner ℂ f g = 0 ∧ 1.999 < Avg_f[g] + Avg_f̂[ĝ]} ≤ 2^{−c₀ n}; reason: 'n large enough' is the n₀; the ∀ g sits inside the bad event
--   - encoding: g compatible with f → ‖g‖ = 1 ∧ inner ℂ f g = 0; reason: the paper's definition on p.13 ('∥g∥ = 1 and ⟨f, g⟩ = 0'); ⟨f,g⟩ = Σ_x f̄(x)g(x)
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Theorem 7, p.45 (Interlude in §5; compatibility p.13; phase states p.12; Avg p.21)

import Definitions.Def_RobustQSC_avg
import Definitions.Def_RobustQSC_phaseLaw

namespace RobustQSC.Supplement

open QAlgorithms MeasureTheory RobustQSC

/-- **Theorem 7 (uncertainty principle for random phase states).** For `n` large enough, for `f` a
random phase function, for all `g` compatible with `f`, `Avg_f[g] + Avg_f̂[ĝ] ≤ 1.999`, except with
probability `2^{−Ω(n)}` over the choice of `f`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Theorem 7, p.45 (Interlude, §5); "g
compatible with f (i.e. ‖g‖ = 1 and ⟨f, g⟩ = 0)", p.13; phase states `|f(x)|² = 2^{−n}`, p.12;
`Avg` defined on p.21.

**Formalization Note.**
1. A random phase function is `f(x) = 2^{−n/2} ω_x` with `(ω_x)_x` i.i.d. Steinhaus, i.e.
   `f ∼ F_µ` for the uniform `µ ≡ 2^{−n}` (the proof, pp.45–46): its law is the published
   `phaseLaw (fun _ => 1 / 2^n)`. Such `f` is a unit vector surely.
2. "For `n` large enough … except with probability `2^{−Ω(n)}`": there are `c₀ > 0` and `n₀`
   such that for every `n ≥ n₀` the probability that **some** compatible `g` violates the bound is
   at most `2^{−c₀ n}`.
3. Compatible is the vector form `‖g‖ = 1 ∧ ⟨f, g⟩ = 0` (`inner ℂ f g = 0`) of p.13. -/
theorem theorem_7 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      phaseLaw (fun _ : Qubits n => 1 / (2 : ℝ) ^ n)
          {f | ∃ g : EuclideanSpace ℂ (Qubits n), IsState g ∧ inner ℂ f g = 0 ∧
            1.999 < avg f g + avg (fourier f) (fourier g)}
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ * n))) := by sorry

end RobustQSC.Supplement
