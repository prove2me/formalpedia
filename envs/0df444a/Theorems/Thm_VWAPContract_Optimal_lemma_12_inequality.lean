-- Prove2me | Theorems.Thm_VWAPContract_Optimal_lemma_12_inequality
-- name    : VWAPContract.Optimal.lemma_12_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:52.989728+00:00
-- url     : https://prove2.me/theorems/fdb7c61e-72af-4b56-8277-727d4c0e0388
-- title:
--   Lemma 12 (4), p. 46 (PDF 47) — $(\sum x_t)(\sum h(x_t/\eta_t)v(x_t,\eta_t))\le(\sum v(x_t,\eta_t))(\sum h(x_t/\eta_t)x_t)$
-- statement:
--   Let $x_t\ge0$ and $\eta_t>0$ for finitely many periods. Suppose $v(x,\eta)>0$, $v(x,\eta)=xV(x/\eta)$ for $x>0$, $V$ is strictly decreasing, and $h$ is strictly increasing. Then
--
--   $$\left(\sum_t x_t\right)\left(\sum_t h(x_t/\eta_t)v(x_t,\eta_t)\right)\le\left(\sum_t v(x_t,\eta_t)\right)\left(\sum_t h(x_t/\eta_t)x_t\right).$$
--
--   This deterministic bound compares the impact component of VWAP with the impact component of the dealer's trading cost. It is the inequality labeled (4) in Lemma 12.
--
--   **Formalization Note** The statement permits an empty finite index, where both sides are zero; schedules in the later equality case are necessarily nonempty.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), p. 46 (PDF 47), Lemma 12, inequality (4)

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem lemma_12_inequality
    (h : ℝ → ℝ) (vol : ℝ → ℝ → ℝ) (V : ℝ → ℝ)
    (hh : StrictMonoOn h (Set.Ici 0))
    (hvpos : ∀ x e, 0 ≤ x → 0 < e → 0 < vol x e)
    (hvform : ∀ x e, 0 < x → 0 < e → vol x e = x * V (x / e))
    (hV : StrictAntiOn V (Set.Ioi 0)) :
    ∀ (n : ℕ) (x e : Fin n → ℝ), (∀ t, 0 ≤ x t) → (∀ t, 0 < e t) →
      (∑ t, x t) * (∑ t, h (x t / e t) * vol (x t) (e t)) ≤
      (∑ t, vol (x t) (e t)) * (∑ t, h (x t / e t) * x t) := by sorry

end VWAPContract.Optimal
