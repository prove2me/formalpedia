-- Prove2me | Theorems.Thm_RealInequalities_loglog_le_rpow
-- name    : RealInequalities.loglog_le_rpow
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:12:02.289289+00:00
-- url     : https://prove2.me/theorems/3660dc83-c20b-4884-9329-cf1cc2042a77
-- title:
--   $\log\log X$ is dominated by $(\log X)^{\theta}$ past a threshold
-- statement:
--   **Any positive power of $\log X$ eventually dominates $\log\log X$.**
--
--   Let $\theta > 0$ and suppose $\log X \ge e$, so that $\log\log X \ge 1$. If additionally the
--   threshold condition
--
--   $$\frac{4}{\theta^{2}} \;\le\; (\log X)^{\theta}$$
--
--   holds, then
--
--   $$\log\log X \;\le\; (\log X)^{\theta}.$$
--
--   Asymptotically this is the familiar statement that $\log t = o(t^{\theta})$ for every
--   $\theta > 0$, applied with $t = \log X$. What the theorem adds is an **explicit and checkable
--   threshold**: rather than "for $X$ sufficiently large", the hypothesis names exactly how large
--   $(\log X)^{\theta}$ must be, namely at least $4/\theta^{2}$.
--
--   That matters in analytic number theory, where $\theta$ is often itself a function of the
--   parameters — shrinking as some other quantity grows — so an implicit "sufficiently large"
--   would be circular. With an explicit gate one can verify the hypothesis at the point of use and
--   keep the estimate effective.
--
--   The constant $4/\theta^2$ comes from applying $\log t \le \tfrac{2}{\theta}\sqrt t$ (valid for
--   $t \ge 1$) with $t = (\log X)^{\theta}$ and then absorbing the square root.
--
--   **Formalization note.** Powers are `Real.rpow`, so $(\log X)^{\theta}$ is defined for real
--   $\theta$; the hypothesis $e \le \log X$ guarantees $\log\log X \ge 1 > 0$.
-- source:
--   Elementary; the effective form of $\log t = o(t^\theta)$ used in analytic number theory. Lean proof extracted from `Salt/MR/USetPins.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace RealInequalities

theorem loglog_le_rpow (X θ : ℝ) (hθ : 0 < θ) (hX : Real.exp 1 ≤ Real.log X)
    (hgate : 4 / θ ^ 2 ≤ (Real.log X) ^ θ) :
    Real.log (Real.log X) ≤ (Real.log X) ^ θ := by sorry

end RealInequalities
