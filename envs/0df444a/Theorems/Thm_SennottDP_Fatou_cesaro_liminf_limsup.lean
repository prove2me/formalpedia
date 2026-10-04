-- Prove2me | Theorems.Thm_SennottDP_Fatou_cesaro_liminf_limsup
-- name    : SennottDP.Fatou.cesaro_liminf_limsup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T12:01:39.226986+00:00
-- url     : https://prove2.me/theorems/970b61c3-d645-4d03-b6ef-5be769a79b73
-- title:
--   Proposition A.1.10 — Cesàro averages lie between the lim inf and lim sup of the sequence
-- statement:
--   Let $(u_n)_{n\ge 0}$ be a sequence of real numbers and let $w_n = \sum_{k=0}^{n-1} u_k$ for $n\ge 1$. Then
--   $$\liminf_{n\to\infty} u_n \;\le\; \liminf_{n\to\infty} \frac{w_n}{n} \;\le\; \limsup_{n\to\infty} \frac{w_n}{n} \;\le\; \limsup_{n\to\infty} u_n. \tag{A.9}$$
--
--   Lower and upper limits may equal $\pm\infty$. The result links the long-run average $w_n/n$ of a cost sequence to the behaviour of the sequence itself, which is how average-cost quantities are compared with per-stage costs.
--
--   **Formalization Note** Lower and upper limits are taken in `EReal`, so no boundedness is assumed. The defining identity for $w_n$ is imposed only for $n\ge 1$, as in the book; $w_0/0$ plays no role in limits along $n\to\infty$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 274, Proposition A.1.10, Eq. (A.9)

import Mathlib

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Proposition A.1.10, p. 274, (A.9). `(u_n)_{n ≥ 0}` is a real sequence and
`w_n = ∑_{k=0}^{n-1} u_k` for `n ≥ 1`. Lower and upper limits are taken in `[−∞, ∞]`:
`liminf u_n ≤ liminf w_n / n ≤ limsup w_n / n ≤ limsup u_n`. -/
theorem cesaro_liminf_limsup (u w : ℕ → ℝ)
    (hw : ∀ n, 1 ≤ n → w n = ∑ k ∈ Finset.range n, u k) :
    liminf (fun n => (u n : EReal)) atTop ≤ liminf (fun n => ((w n / n : ℝ) : EReal)) atTop ∧
    liminf (fun n => ((w n / n : ℝ) : EReal)) atTop ≤
      limsup (fun n => ((w n / n : ℝ) : EReal)) atTop ∧
    limsup (fun n => ((w n / n : ℝ) : EReal)) atTop ≤ limsup (fun n => (u n : EReal)) atTop := by sorry

end SennottDP.Fatou
