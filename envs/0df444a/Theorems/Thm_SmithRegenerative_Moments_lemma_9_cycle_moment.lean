-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_lemma_9_cycle_moment
-- name    : SmithRegenerative.Moments.lemma_9_cycle_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:35:04.301984+00:00
-- url     : https://prove2.me/theorems/5a660b17-a655-461f-93fe-642022650299
-- title:
--   Lemma 9 — moment of the cycle containing time t
-- statement:
--   Let $(w_t)$ be a cumulative process with cycle lengths $t_n$, cycle increments $y_n=w_{T_n}-w_{T_{n-1}}$, and let $n_t$ be the number of renewal epochs in $[0,t]$, so that cycle $n_t$, the interval $[T_{n_t-1},T_{n_t})$, contains $t$. If $p>0$ and $\mathbb E|y_1|^p<\infty$, then $|y_{n_t}|^p$ is integrable for every $t\geq0$, and
--
--   $$
--   \mathbb E|y_{n_t}|^{p}=o(t)\qquad(t\to\infty).
--   $$
--
--   The cycle containing $t$ is length-biased, so its moment is not $\mathbb E|y_1|^p$; the lemma says it still grows sublinearly. Applied to the variation process $\tilde w_t$, whose cycle increments are $\tilde y_n$, it controls the incomplete-cycle remainder in both parts of Theorem 8.
--
--   **Formalization Note** Smith writes $\mathbb E y_1^p$ for real $p>0$ and his proof integrates from $0-$, i.e. treats a nonnegative cycle quantity. The statement is taken for $|y_n|^p$: it is the printed lemma when $y\ge0$ (in particular for $\tilde y$) and the meaningful $p$th moment for a signed increment. The power is the real power `Real.rpow` of a nonnegative number.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 28, Lemma 9

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_CumulativeProcess

namespace SmithRegenerative.Moments

open MeasureTheory Filter

/-- Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), p. 28, Lemma 9.
Formalization Note: the paper writes `Ey₁^p` for a real `p > 0` without saying
`y₁ ≥ 0`; its proof integrates from `0−`, i.e. treats a nonnegative cycle
quantity. The statement is taken for `|y_n|^p`, which is the printed lemma when
`y ≥ 0` and the meaningful `p`th moment for a signed `y`. Theorem 8 applies it to
the cumulative process `w̃` (whose cycle increments are the `ỹ_n ≥ 0`).
`y_{n_t}` is the increment of cycle `n_t`, the cycle `[T_{n_t-1}, T_{n_t})`
containing `t`. -/
theorem lemma_9_cycle_moment {Ω : Type*} [MeasurableSpace Ω]
    (C : CumulativeProcess Ω) (p : ℝ) (hp : 0 < p)
    (hκp : Integrable
      (fun ω => |cycleReward C.renewal C.w 1 ω| ^ p) C.renewal.P) :
    (∀ t : ℝ, 0 ≤ t → Integrable
      (fun ω => |cycleReward C.renewal C.w (C.renewal.count t ω) ω| ^ p)
        C.renewal.P) ∧
    (fun t : ℝ =>
      ∫ ω, |cycleReward C.renewal C.w (C.renewal.count t ω) ω| ^ p
        ∂C.renewal.P) =o[atTop] (fun t : ℝ => t) := by sorry

end SmithRegenerative.Moments
