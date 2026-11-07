-- Prove2me | Theorems.Thm_RobustQSC_theorem_4
-- name    : RobustQSC.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:44.868876+00:00
-- url     : https://prove2.me/theorems/b7228b2c-66dc-44d7-9b11-6f92ad745956
-- title:
--   Theorem 4, p.21 — the uncertainty principle $\mathrm{Avg}_f[g]+\mathrm{Avg}_{\hat f}[\hat g]\le2-c$
-- statement:
--   With probability at least $1-2^{-\Omega(n)}$ over a Haar-random $f:\{0,1\}^n\to\mathbb C$ with $\|f\|_2=1$, for all $g:\{0,1\}^n\to\mathbb C$ with $\|g\|_2=1$ and $\langle f,g\rangle=0$,
--
--   $$
--   \mathrm{Avg}_f[g]+\mathrm{Avg}_{\hat f}[\hat g]\le2-c,
--   $$
--
--   where $c>0$ is a universal constant independent of $n$.
--
--   Since $\mathrm{Avg}_f[f]+\mathrm{Avg}_{\hat f}[\hat f]=2$, this is a spectral gap below the top eigenvector. It is the analytic core of the paper.
--
--   Differences from the source:
--   - encoding: "with probability $1-2^{-\Omega(n)}$", "for $n$ large" → a constant $c_0>0$ and a threshold $n_0$ with the outer measure of the failure event at most $2^{-c_0n}$ for $n\ge n_0$; reason: the standard meaning; the failure event is bounded in outer measure, so no measurability is assumed
--   - encoding: $\langle f,g\rangle=\sum_x\overline{f(x)}g(x)$ → `inner ℂ f g`; reason: same form
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Theorem 4, p.21; proof, §8, pp.73–76

import Definitions.Def_RobustQSC_avg
import Definitions.Def_QAlgorithms_Defs_HaarTargetStates

namespace RobustQSC

open QAlgorithms QAlgorithms.TwoBasisCertification MeasureTheory

/-- **Theorem 4 (The uncertainty principle).** With probability at least `1 − 2^{−Ω(n)}` over
a Haar-random `f : {0,1}ⁿ → ℂ`, `‖f‖₂ = 1`, for all `g : {0,1}ⁿ → ℂ` with `‖g‖₂ = 1` and
`⟨f, g⟩ = 0`, `Avg_f[g] + Avg_f̂[ĝ] ≤ 2 − c`, where `c > 0` is a universal constant independent of
`n`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Theorem 4, p.21 (overview form p.9); proof, §8, pp.73–76.

**Formalization Note.** `c` and the `Ω(n)` constant `c₀` are chosen before `n`, for `n ≥ n₀`; the
bad event is "some admissible `g` violates the bound" (the `∀ g` is inside the event).
`⟨f, g⟩ = Σ_x f̄(x) g(x)` is `inner ℂ f g`. -/
theorem theorem_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      haarTargetLaw n {f | IsState f ∧ ∃ g : EuclideanSpace ℂ (Qubits n), IsState g ∧
          inner ℂ f g = 0 ∧ 2 - c < avg f g + avg (fourier f) (fourier g)}
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ * n))) := by sorry

end RobustQSC
