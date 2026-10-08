-- Prove2me | Theorems.Thm_SuttonTD_Convergence_theorem_1
-- name    : SuttonTD.Convergence.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:06.053982+00:00
-- url     : https://prove2.me/theorems/1f817bd9-c41f-4acc-bf75-5c6220328ca0
-- title:
--   Theorem 1 — linear TD(1) and Widrow–Hoff produce the same per-sequence weight changes
-- statement:
--   For every sequence of observation vectors $x_1,\dots,x_m\in\mathbb R^K$, outcome $z$, weight vector $w$ (held fixed during the sequence) and step size $\alpha$,
--
--   $$\sum_{t=1}^m\alpha\,(z-w^\top x_t)\,x_t=\sum_{t=1}^m\alpha\,(P_{t+1}-P_t)\sum_{k=1}^t x_k,$$
--
--   where $P_t=w^\top x_t$ for $t\le m$ and $P_{m+1}=z$. That is, on multi-step prediction problems the linear TD(1) procedure produces the same per-sequence weight changes as the Widrow–Hoff procedure.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §2.2, Theorem 1, p. 15 (PDF p. 7)

import Definitions.Def_SuttonTD_Convergence_PerSequenceChanges

namespace SuttonTD.Convergence

/-- **Theorem 1** (Sutton 1988, §2.2, p. 15, PDF p. 7): "On multi-step prediction problems, the
linear TD(1) procedure produces the same per-sequence weight changes as the Widrow-Hoff
procedure." For every sequence of observation vectors `x_1, …, x_m`, outcome `z`, weight vector
`w` (fixed during the sequence) and step size `α`,
`∑_{t=1}^m α (z − wᵀx_t) x_t = ∑_{t=1}^m α (P_{t+1} − P_t) ∑_{k=1}^t x_k`,
with `P_t = wᵀx_t` and `P_{m+1} = z`. -/
theorem theorem_1 {K : ℕ} (m : ℕ) (xs : ℕ → Fin K → ℝ) (z α : ℝ) (w : Fin K → ℝ) :
    widrowHoffChange m xs z α w = tdOneChange m xs z α w := by sorry

end SuttonTD.Convergence
