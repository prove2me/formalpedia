-- Prove2me | Theorems.Thm_RobustQSC_theorem_5
-- name    : RobustQSC.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:24.026898+00:00
-- url     : https://prove2.me/theorems/9f9d88a1-d910-4564-83d7-2bc64980deae
-- title:
--   Theorem 5, p.22 — concentration of $\mathrm{Avg}_{\hat f}[\widehat{fq}]$ for fixed $q$
-- statement:
--   There exists a universal constant $c>0$ such that for all $t>0$, with probability $1-\exp(-\Omega(n))$ over $\mu\sim\boldsymbol\mu$, for any $\mu$-compatible $q$ satisfying $\max_x\mu(x)|q(x)|^2\le\|\mu\|_\infty^{1/3}$,
--
--   $$
--   \Pr_{f\sim F_\mu}\Bigl[\mathrm{Avg}_{\hat f}[\widehat{fq}]\ge\frac12+t+o(1)\Bigr]\le\exp\bigl(-ct^6N^{1/3-o(1)}\bigr),\qquad N=2^n.
--   $$
--
--   The bound is doubly exponential in $n$, strong enough to survive a union bound over a net of size $\exp(N^{H(\gamma)+o(1)})$ with $H(\gamma)<1/3$.
--
--   Differences from the source:
--   - reading: the constants of $\Omega(n)$ and the two $o(1)$ are unspecified → $c$ is chosen before $t$; $c_0$, the sequences $e_1,e_2\to0$ and $n_0$ are chosen after $t$ and before $n$, uniformly in $\mu$ and $q$; reason: the proof (p.45) says "for fixed $t>0$ and all sufficiently large $n$", and §8 uses one value of $t$
--   - encoding: $\|\mu\|_\infty$ → $\sup_x\mu(x)$; reason: same quantity on a finite set
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Theorem 5, p.22; proof, pp.44–45

import Definitions.Def_RobustQSC_dirichletOne
import Definitions.Def_RobustQSC_phaseLaw
import Definitions.Def_RobustQSC_avg
import Definitions.Def_RobustQSC_Compatible

namespace RobustQSC

open QAlgorithms MeasureTheory Filter Topology

/-- **Theorem 5 (Concentration of `Avg_f̂[\widehat{fq}]` for fixed `q`).** There is a
universal constant `c > 0` such that for all `t > 0`, with probability `1 − exp(−Ω(n))` over
`μ ∼ 𝛍`, every `μ`-compatible `q` with `max_x μ(x)|q(x)|² ≤ ‖μ‖_∞^{1/3}` satisfies
`Pr_{f∼F_μ}[Avg_f̂[\widehat{fq}] ≥ ½ + t + o(1)] ≤ exp(−c t⁶ N^{1/3−o(1)})`, `N = 2ⁿ`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Theorem 5, p.22; proof, pp.44–45 ("For fixed t > 0 and all sufficiently large n").

**Formalization Note.** `c` is chosen before `t`; the constant `c₀` of `Ω(n)`, the two `o(1)`
sequences `e₁, e₂ → 0` and the threshold `n₀` are chosen after `t` and before `n`, uniformly in
`μ` and `q`. `‖μ‖_∞ = ⨆_x μ(x)`. The bad `μ`-event is "the bound fails for some admissible
`q`". -/
theorem theorem_5 :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ e₁ e₂ : ℕ → ℝ,
      Tendsto e₁ atTop (𝓝 0) ∧ Tendsto e₂ atTop (𝓝 0) ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        dirichletOne (Qubits n) {μ | ¬ ∀ q : Qubits n → ℂ, Compatible μ q →
            (∀ x, μ x * ‖q x‖ ^ 2 ≤ (⨆ y, μ y) ^ (1 / 3 : ℝ)) →
            phaseLaw μ {f | 1 / 2 + t + e₁ n ≤ avg (fourier f) (fourier (ptMul f q))} ≤
              ENNReal.ofReal (Real.exp (-(c * t ^ 6 * ((2 : ℝ) ^ n) ^ (1 / 3 - e₂ n))))}
          ≤ ENNReal.ofReal (Real.exp (-(c₀ * n))) := by sorry

end RobustQSC
