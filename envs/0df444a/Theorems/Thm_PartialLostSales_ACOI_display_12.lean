-- Prove2me | Theorems.Thm_PartialLostSales_ACOI_display_12
-- name    : PartialLostSales.ACOI.display_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:01.184615+00:00
-- url     : https://prove2.me/theorems/a786819b-9271-421d-a274-5c8653e36167
-- title:
--   (12), corrected, pp. 13–14 — v_α(δ0) − v^π_α(z′) ≤ C̄ uniformly in α ∈ [α∗,1), beliefs z′ and stationary policies π
-- statement:
--   Consider the COMDP of the lost-sales inventory model observed only at zero, under the standing assumptions. Then there are $\alpha_*\in(0,1)$ and $\bar C<\infty$ such that, uniformly in $\alpha\in[\alpha_*,1)$, in beliefs $z'$ with finite second moment, and in all stationary policies $\pi$,
--   $$v_\alpha(\delta_0)-v^\pi_\alpha(z')\ \le\ \bar C\qquad\text{whenever }v^\pi_\alpha(z')<\infty .$$
--   Here $v_\alpha(\delta_0)$ is the optimal discounted cost from the belief $\delta_0$ (inventory known to be $0$), and $v^\pi_\alpha(z')$ is the discounted cost of $\pi$ from $z'$.
--
--   **Correction.** The paper prints the first term as $v^\pi_\alpha(\delta_0)$, the cost of the same stationary policy started at $\delta_0$. Its proof (§4.1–4.2) instead bounds the cost of a different policy started at $\delta_0$, the *pursuing policy*, which tracks the process started at $z'$. What is used to derive (11) is the bound on the optimal value $v_\alpha(\delta_0)$. The printed form, with the same stationary $\pi$ at $\delta_0$, is not what the proof establishes. This statement is the corrected one.
--
--   (12) gives (11): take $\pi$ discount-optimal and stationary (Lemma 1); then $v_\alpha(\delta_0)-m_\alpha\le\bar C$.
--
--   **Formalization Note.** $\bar C$ is taken in $[0,\infty)$, which loses nothing. The inequality is stated as $v_\alpha(\delta_0)\le v^\pi_\alpha(z')+\bar C$ in $[0,\infty]$; it is trivially true when $v^\pi_\alpha(z')=\infty$, so the side condition is not needed. Stationary policies are measurable maps from beliefs to $[0,K]$.
-- source:
--   Bai, Chen & Stolyar, Average Cost Optimality in Partially Observed Lost-Sales Inventory Systems, SSRN preprint 3865728, pp. 13–14, display (12) (corrected: v_α(δ0) for the printed v^π_α(δ0))

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE
open scoped ENNReal NNReal

namespace PartialLostSales.ACOI

/-- Display (12), pp. 13–14, corrected (the printed first term `v^π_α(δ₀)` is read as the
optimal value `v_α(δ₀)`): there are `α* ∈ (0, 1)` and `C̄ < ∞` such that, uniformly in
`α ∈ [α*, 1)`, in beliefs `z'` with finite second moment and in stationary policies `π`,
`v_α(δ₀) − v^π_α(z') ≤ C̄` whenever `v^π_α(z') < ∞`. -/
theorem display_12 (P : Params) (hP : Standing P) (M : MDP (Bel P) (Act P))
    (hM : IsCOMDP P M) :
    ∃ αstar ∈ Set.Ioo (0 : ℝ) 1, ∃ Cbar : ℝ≥0,
      ∀ α ∈ Set.Ico αstar 1, ∀ z' : Bel P, ∀ φ : Bel P → Act P, ∀ hφ : Measurable φ,
        vOpt M α (δ0 P) ≤ vDisc M (Policy.ofStationary φ hφ) α z' + (Cbar : ℝ≥0∞) := by sorry

end PartialLostSales.ACOI
