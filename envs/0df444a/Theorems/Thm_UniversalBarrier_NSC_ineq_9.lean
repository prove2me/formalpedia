-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_ineq_9
-- name    : UniversalBarrier.NSC.ineq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:41.028102+00:00
-- url     : https://prove2.me/theorems/350ceda5-03de-41b9-a130-3360393615f5
-- title:
--   Inequality (9), p. 6 — ℓ(t) ≤ 2√(n+1) for every real t
-- statement:
--   Let $n\ge1$, $c_n=\dfrac{n-1}{2\sqrt n}$ and
--   $$\ell(t)=\frac{2t^3+6t+4c_n}{(1+t^2)^{3/2}}\qquad(t\in\mathbb R).$$
--   Then for every $t\in\mathbb R$,
--   $$\ell(t)\ \le\ 2\sqrt{n+1}.$$
--
--   Combined with (8), this bound gives $|D^3\varphi(x)[h,h,h]|\le2(D^2\varphi(x)[h,h])^{3/2}$, the self-concordance inequality (1) in the proof of Theorem 2. The maximum is attained at $t=1/\sqrt n$.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, pp. 5–6, definition of c_n and ℓ, inequality (9)

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

namespace UniversalBarrier.NSC

theorem ineq_9 (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : ell n t ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by sorry

end UniversalBarrier.NSC
