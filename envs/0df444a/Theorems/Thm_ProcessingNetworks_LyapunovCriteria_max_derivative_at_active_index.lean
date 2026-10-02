-- Prove2me | Theorems.Thm_ProcessingNetworks_LyapunovCriteria_max_derivative_at_active_index
-- name    : ProcessingNetworks.LyapunovCriteria.max_derivative_at_active_index
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:59:32.025533+00:00
-- url     : https://prove2.me/theorems/28aa2313-0653-4393-a977-0915f62888f8
-- title:
--   Lemma 8.10 — derivative of a pointwise maximum (milestone)
-- statement:
--   **Lemma 8.10.** Let $f_1,\dots,f_d : \mathbb{R}_+ \to \mathbb{R}$ and
--   $f(t) := \max_{j=1,\dots,d} f_j(t)$. Fix $t > 0$ and $i$ with $f_i(t) = f(t)$. If $f_i$ and
--   $f$ are both differentiable at $t$, then $\dot f(t) = \dot f_i(t)$.
--
--   This is the calculus fact behind piecewise-linear (max-of-linear-functions) Lyapunov
--   functions: at a point where the maximum is attained by a particular index, and both the
--   maximum and that component happen to be differentiable, they share the same derivative there
--   — used, per the book's own remark, "when the function $H$ in (8.1) is piecewise linear" (the
--   max-weight Lyapunov functions of Chapters 8-9).
--
--   **Formalization note.** The maximum is formalized as `⨆ j, f j t`, a supremum over the
--   *finite* index type `Fin d` — always a genuine maximum (no risk of the junk-value behavior a
--   supremum over an unbounded or infinite index could exhibit), matching `max_{j=1,...,d} f_j(t)`
--   exactly.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 138, Lemma 8.10

import Mathlib

namespace ProcessingNetworks.LyapunovCriteria

/-- Lemma 8.10, Dai & Harrison p. 138 (PDF p. 154): for functions `f_j : ℝ_+ → ℝ`,
`j = 1,…,d`, let `f(t) := max_j f_j(t)`. Fix `t > 0` and `i` with `f_i(t) = f(t)`; if `f_i` and
`f` are both differentiable at `t`, then `ḟ(t) = ḟ_i(t)`. -/
theorem max_derivative_at_active_index
    {d : ℕ} (f : Fin d → ℝ → ℝ) (t : ℝ) (ht : 0 < t) (i : Fin d)
    (hi : f i t = ⨆ j, f j t)
    (hfi : DifferentiableAt ℝ (f i) t) (hmax : DifferentiableAt ℝ (fun s => ⨆ j, f j s) t) :
    deriv (fun s => ⨆ j, f j s) t = deriv (f i) t := by sorry

end ProcessingNetworks.LyapunovCriteria
