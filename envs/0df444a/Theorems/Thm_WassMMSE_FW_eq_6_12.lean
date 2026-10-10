-- Prove2me | Theorems.Thm_WassMMSE_FW_eq_6_12
-- name    : WassMMSE.FW.eq_6_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:08.435409+00:00
-- url     : https://prove2.me/theorems/bb136246-3574-46ce-a9d8-8a933b31f01b
-- title:
--   (6.12), p. 25, corrected — case (ii) of Algorithm 1: h_{t+1} ≤ (1 − (1 − √(1 − δ))²αε/(4β̄))h_t
-- statement:
--   In the setting of Section 6.1 (a product $\mathcal S=\times_k\mathcal S^{[k]}$ of convex compact sets, $f$ convex on $\mathcal S$ and differentiable at its points with optimal value $f^\star=\min_{\mathcal S}f$, an inexact oracle $F$ with precision $\delta\in[0,1]$), assume Assumption 6.1: $f$ is $\beta$-smooth, the marginal feasible sets are $\alpha$-strongly convex with respect to $f$, and $f$ is $\varepsilon$-steep. Let $(s_t,\beta_t,\eta_t)_{t\ge0}$ be a run of Algorithm 1 with inputs $\beta_{-1}>0$, $\tau>1$, $\zeta>1$, let $\bar\beta=\max\{\tau\beta,\beta_{-1}\}$, and write $h_t=f(s_t)-f^\star$, $d_t=F(s_t)-s_t$, $g_t=-d_t^\top\nabla f(s_t)$. If at iteration $t$
--
--   $$\frac{g_t}{\beta_t\|d_t\|^2}<1\qquad\text{(case (ii))},$$
--
--   then
--
--   $$h_{t+1}\le\Big(1-\frac{\big(1-\sqrt{1-\delta}\big)^2\alpha\varepsilon}{4\bar\beta}\Big)h_t .$$
--
--   This is the second of the two contraction factors in Theorem 6.2.
--
--   **Formalization Note** The paper prints the factor as $1-(1-\sqrt{1-\delta})\alpha\varepsilon/(4\bar\beta)$, without the square; the error is inherited from Lemma 6.3 (ii), whose printed constant drops a square (see that item). The two agree at $\delta=1$. In Lean's arithmetic $x/0=0$, so the case hypothesis also covers $d_t=0$, which the page leaves undefined; the bound holds there too.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 25, (6.12), case (ii) of the proof of Theorem 6.2 (constant corrected; see Formalization Note)

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-- (6.12), case (ii) of the proof of Theorem 6.2, p. 25, **with the corrected constant**: under
Assumption 6.1, along every run of Algorithm 1, if `g_t/(β_t‖d_t‖²) < 1` then
`h_{t+1} ≤ (1 − (1 − √(1 − δ))² αε/(4β̄)) h_t` with `β̄ = max{τβ, β_{−1}}`. The page prints
`(1 − √(1 − δ))` without the square, inherited from Lemma 6.3 (ii). -/
theorem eq_6_12
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {β α ε : ℝ} (hβ : IsSmoothOn S f β) (hα : IsStronglyConvexWrt S Sk f α) (hε : IsSteep S f ε)
    {βm1 τ ζ : ℝ} {s : ℕ → BlockSpace K d} {βt ηt : ℕ → ℝ}
    (hrun : IsFAFWRun S f F βm1 τ ζ s βt ηt) {fstar : ℝ} (hfstar : IsLeast (f '' S) fstar)
    (t : ℕ) (hcase : fwGap f F (s t) / (βt t * ‖fwDirection F (s t)‖ ^ 2) < 1) :
    f (s (t + 1)) - fstar
      ≤ (1 - (1 - Real.sqrt (1 - δ)) ^ 2 * α * ε / (4 * max (τ * β) βm1)) * (f (s t) - fstar) := by sorry

end WassMMSE.FW
