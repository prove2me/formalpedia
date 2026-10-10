-- Prove2me | Theorems.Thm_WassMMSE_FW_eq_6_11
-- name    : WassMMSE.FW.eq_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:27.480487+00:00
-- url     : https://prove2.me/theorems/73c46c63-42eb-42ef-ad39-81b956166c05
-- title:
--   (6.11), p. 25 — case (i) g_t/(β_t‖d_t‖²) ≥ 1 of Algorithm 1: h_{t+1} ≤ −g_t/2 + h_t ≤ (1 − δ/2)h_t
-- statement:
--   In the setting of Section 6.1 (a product $\mathcal S$ of convex compact sets, $f$ convex on $\mathcal S$ and differentiable at its points with optimal value $f^\star=\min_{\mathcal S}f$, an inexact oracle $F$ with precision $\delta\in[0,1]$), let $(s_t,\beta_t,\eta_t)_{t\ge0}$ be a run of Algorithm 1, and write $h_t=f(s_t)-f^\star$, $d_t=F(s_t)-s_t$, $g_t=-d_t^\top\nabla f(s_t)$. If at iteration $t$
--
--   $$\frac{g_t}{\beta_t\|d_t\|^2}\ge1\qquad\text{(case (i))},$$
--
--   then (the stepsize being $\eta_t=1$ in this case)
--
--   $$h_{t+1}\le-\frac{g_t}{2}+h_t\qquad\text{and}\qquad h_{t+1}\le\Big(1-\frac{\delta}{2}\Big)h_t .$$
--
--   This is the first of the two contraction factors in Theorem 6.2.
--
--   **Formalization Note** In Lean's arithmetic $x/0=0$, so the case hypothesis forces $d_t\neq0$.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 25, (6.11), case (i) of the proof of Theorem 6.2

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-- (6.11), case (i) of the proof of Theorem 6.2, p. 25: along every run of Algorithm 1, if
`g_t/(β_t‖d_t‖²) ≥ 1` then `h_{t+1} ≤ −g_t/2 + h_t` and `h_{t+1} ≤ (1 − δ/2) h_t`. -/
theorem eq_6_11
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {βm1 τ ζ : ℝ} {s : ℕ → BlockSpace K d} {βt ηt : ℕ → ℝ}
    (hrun : IsFAFWRun S f F βm1 τ ζ s βt ηt) {fstar : ℝ} (hfstar : IsLeast (f '' S) fstar)
    (t : ℕ) (hcase : 1 ≤ fwGap f F (s t) / (βt t * ‖fwDirection F (s t)‖ ^ 2)) :
    f (s (t + 1)) - fstar ≤ -(fwGap f F (s t) / 2) + (f (s t) - fstar) ∧
      f (s (t + 1)) - fstar ≤ (1 - δ / 2) * (f (s t) - fstar) := by sorry

end WassMMSE.FW
