-- Prove2me | Theorems.Thm_ParallelSU2_Reduction_buzek_optimum
-- name    : ParallelSU2.Reduction.buzek_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:19.785012+00:00
-- url     : https://prove2.me/theorems/d6b67dae-015b-47c8-902e-5798892930e9
-- title:
--   Eq. (11), made exact — min ½(1 − Σ a_k a_{k−1}) over a ≥ 0, Σa_k² = 1 is sin²(π/(2(n+2))); n² times it → π²/4
-- statement:
--   For $n\in\mathbb N$ consider real coefficients $a_0,\dots,a_n\ge0$ with $\sum_{k=0}^na_k^2=1$. The phase-estimation optimum
--   $$\mathcal D^n_{\rm opt}=\min\Big\{\tfrac12\Big(1-\sum_{k=1}^na_ka_{k-1}\Big)\Big\}$$
--   is attained and equals
--   $$\mathcal D^n_{\rm opt}=\sin^2\frac{\pi}{2(n+2)},$$
--   and
--   $$\lim_{n\to\infty}n^2\,\sin^2\frac{\pi}{2(n+2)}=\frac{\pi^2}{4}.$$
--
--   This is Bužek, Derka and Massar's optimal phase estimate, quoted by the paper as $\mathcal D^n_{\rm opt}\cong\pi^2/(4n^2)$, in exact form; with $n=d-1$ it is the optimum of the method value $v(x)$ of the SU(2) protocol.
--
--   **Made exact.** The paper's "$\cong$" is replaced by the exact minimum and the limit. The quoted coefficient vector $a_k=\sqrt{2/(n+1)}\sin(\pi(k+1/2)/(n+1))$ is not the minimizer (the minimizer is proportional to $\sin(\pi(k+1)/(n+2))$), so it is not part of the statement.
-- source:
--   Hayashi, Parallel Treatment of Estimation of SU(2) and Phase Estimation, arXiv:quant-ph/0407053v3, p. 5, eq. (11) and the display before it (cited from Bužek et al. [1])

import Mathlib
open Filter Topology

namespace ParallelSU2.Reduction

/-- Hayashi p. 5, eq. (11) (Bužek et al.), in exact form: the minimum of
`½(1 − ∑_{k=1}^n a_k a_{k−1})` over `a_0, …, a_n ≥ 0` with `∑ a_k² = 1` is `sin²(π/(2(n+2)))`,
and `n² · sin²(π/(2(n+2))) → π²/4`. -/
theorem buzek_optimum :
    (∀ n : ℕ, IsLeast
      {v : ℝ | ∃ a : Fin (n + 1) → ℝ, (∀ k, 0 ≤ a k) ∧ ∑ k, a k ^ 2 = 1 ∧
        v = (1 / 2 : ℝ) * (1 - ∑ k : Fin n, a k.castSucc * a k.succ)}
      (Real.sin (Real.pi / (2 * ((n : ℝ) + 2))) ^ 2)) ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * Real.sin (Real.pi / (2 * ((n : ℝ) + 2))) ^ 2) atTop
      (𝓝 (Real.pi ^ 2 / 4)) := by sorry

end ParallelSU2.Reduction
