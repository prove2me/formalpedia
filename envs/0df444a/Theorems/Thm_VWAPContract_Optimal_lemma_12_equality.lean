-- Prove2me | Theorems.Thm_VWAPContract_Optimal_lemma_12_equality
-- name    : VWAPContract.Optimal.lemma_12_equality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:48.766561+00:00
-- url     : https://prove2.me/theorems/14340fff-7fc3-4a45-a146-53768cacb830
-- title:
--   Lemma 12 (equality in (4)), p. 46 (PDF 47) — for $\sum x_t=1$, equality iff $x_t=\eta_t/\sum_s\eta_s$
-- statement:
--   Under the hypotheses of Lemma 12, suppose $x$ is a trading schedule: $x_t\ge0$ and $\sum_t x_t=1$. Equality in the weighted impact inequality
--
--   $$\left(\sum_t x_t\right)\left(\sum_t h(x_t/\eta_t)v(x_t,\eta_t)\right)=\left(\sum_t v(x_t,\eta_t)\right)\left(\sum_t h(x_t/\eta_t)x_t\right)$$
--
--   holds if and only if $x_t=\eta_t/\sum_s\eta_s$ for every period. This identifies the sole schedule where the impact comparison is tight and supplies strict dealer incentives away from volume participation.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), p. 46 (PDF 47), Lemma 12, second sentence (equality case of (4))

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem lemma_12_equality
    (h : ℝ → ℝ) (vol : ℝ → ℝ → ℝ) (V : ℝ → ℝ)
    (hh : StrictMonoOn h (Set.Ici 0))
    (hvpos : ∀ x e, 0 ≤ x → 0 < e → 0 < vol x e)
    (hvform : ∀ x e, 0 < x → 0 < e → vol x e = x * V (x / e))
    (hV : StrictAntiOn V (Set.Ioi 0)) :
    ∀ (n : ℕ) (x e : Fin n → ℝ), IsSchedule x → (∀ t, 0 < e t) →
      ((∑ t, x t) * (∑ t, h (x t / e t) * vol (x t) (e t)) =
        (∑ t, vol (x t) (e t)) * (∑ t, h (x t / e t) * x t) ↔
        ∀ t, x t = xFB e t) := by sorry

end VWAPContract.Optimal
