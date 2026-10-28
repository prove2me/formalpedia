-- Prove2me | Theorems.Thm_SinglePointPricing_Det_lemma_C_2
-- name    : SinglePointPricing.Det.lemma_C_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:33.741155+00:00
-- url     : https://prove2.me/theorems/2fb27b92-52c1-45f8-b945-7867c459f1d9
-- title:
--   Lemma C-2, p. App-5 — r is an optimal price of the worst-case law F_α(·|r,(w,q)) for r ∈ [r̲_α, w) ∪ [w, r̄_α]
-- statement:
--   Let $\alpha\in[0,1]$, $w>0$, $q\in(0,1)$ and $r\in[\underline r_\alpha(w,q),w)\cup[w,\overline r_\alpha(w,q)]$. Then $r\ge0$ is an optimal price of $F_\alpha(\cdot\mid r,(w,q))$:
--   $$r\,\overline F_\alpha(r\mid r,(w,q)) = \max_{v\ge0} v\,\overline F_\alpha(v\mid r,(w,q)).$$
--
--   Consequently $\mathrm{opt}(F_\alpha(\cdot\mid r,(w,q)))$ is the revenue at $r$, which equals $r$ when $r<w$; this is step (a) of (4.1).
--
--   Differences from the source:
--   - reading: 'the optimal price associated with F_α(·|r, (w, q)) is given by r' → r maximizes v ↦ v F̄_α(v|r, (w, q)) over v ≥ 0; reason: the uniqueness reading is false: for α = 0 and r = r̲_0(w, q) the revenue v F̄_0(v|r, (w, q)) equals r on all of [r, w]
--   - encoding: r ≤ r̄_α(w, q) = w/(αΓ_α^{−1}(q)), with r̄_0 = +∞ → α Γ_α^{−1}(q) r ≤ w; reason: Γ_α^{−1}(q) > 0 for q ∈ (0, 1), so the condition is the same, and at α = 0 it is r < +∞
--   - encoding: r ≥ 0 implicit → conclusion r ∈ [0, ∞) stated; reason: the optimal price is a price; r̲_α(w, q) > 0
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Lemma C-2, p. App-5

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

/-- Lemma C-2, p. App-5: for `α ∈ [0, 1]`, `w > 0`, `q ∈ (0, 1)` and
`r ∈ [r̲_α(w, q), w) ∪ [w, r̄_α(w, q)]`, the price `r` is an optimal price of `F_α(·|r, (w, q))`:
it maximizes the revenue `v ↦ v F̄_α(v|r, (w, q))` over `v ≥ 0`. -/
theorem lemma_C_2 (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ rSet α w q) :
    r ∈ Set.Ici (0 : ℝ) ∧ IsMaxOn (fun v => v * Fbar α w q r v) (Set.Ici 0) r := by sorry

end SinglePointPricing.Det
