-- Prove2me | Theorems.Thm_WassMMSE_FW_eq_6_10
-- name    : WassMMSE.FW.eq_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:03.079991+00:00
-- url     : https://prove2.me/theorems/a7643670-60f4-445c-b4b9-ab52e7509b75
-- title:
--   (6.10), p. 25 — along Algorithm 1, h_{t+1} ≤ −η_t g_t + ½β_tη_t²‖d_t‖² + h_t
-- statement:
--   In the setting of Section 6.1 (a product $\mathcal S$ of convex compact sets, $f$ convex on $\mathcal S$ and differentiable at its points with optimal value $f^\star=\min_{\mathcal S}f$, an inexact oracle $F$ with precision $\delta\in[0,1]$), let $(s_t,\beta_t,\eta_t)_{t\ge0}$ be a run of the fully adaptive Frank-Wolfe algorithm (Algorithm 1), and write $h_t=f(s_t)-f^\star$, $d_t=F(s_t)-s_t$ and $g_t=-d_t^\top\nabla f(s_t)$. Then for every $t\ge0$
--
--   $$h_{t+1}\le-\eta_tg_t+\tfrac12\beta_t\eta_t^2\|d_t\|^2+h_t .$$
--
--   This one-step bound is the common starting point of the two cases of the proof of Theorem 6.2.
--
--   **Formalization Note** The paper prints the right-hand side with $-g_t$ instead of $-\eta_tg_t$. What the sufficient-decrease condition (6.5) gives is $-\eta_tg_t$; the printed form coincides with it in case (i), where $\eta_t=1$, and the proof of case (ii) restores the factor $\eta_t$ ("from multiplying $-g_t$ with $\eta_t<1$"). The statement is (6.10) in the form (6.5) gives it. The identity $h_{t+1}=f(s_t+\eta_td_t)-f(s_t)+h_t$ of the display is immediate and is not restated.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 25, (6.10), proof of Theorem 6.2 (with −η_t g_t; see Formalization Note)

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-- (6.10), proof of Theorem 6.2, p. 25, in the form (6.5) gives it: along every run of Algorithm 1,
`h_t = f(s_t) − f⋆` satisfies `h_{t+1} ≤ −η_t g_t + ½β_tη_t²‖d_t‖² + h_t`. -/
theorem eq_6_10
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {βm1 τ ζ : ℝ} {s : ℕ → BlockSpace K d} {βt ηt : ℕ → ℝ}
    (hrun : IsFAFWRun S f F βm1 τ ζ s βt ηt) {fstar : ℝ} (hfstar : IsLeast (f '' S) fstar) :
    ∀ t : ℕ, f (s (t + 1)) - fstar
      ≤ -(ηt t * fwGap f F (s t)) + βt t * ηt t ^ 2 / 2 * ‖fwDirection F (s t)‖ ^ 2
          + (f (s t) - fstar) := by sorry

end WassMMSE.FW
