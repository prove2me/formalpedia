-- Prove2me | Theorems.Thm_VWAPContract_Optimal_lemma_3_jensen
-- name    : VWAPContract.Optimal.lemma_3_jensen
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:46.924341+00:00
-- url     : https://prove2.me/theorems/a28e202c-c36e-4379-a667-4234df822fda
-- title:
--   Proof of Lemma 3, p. 50 (PDF 51) — Jensen step: $\sum_t h(x_t/\eta_t)x_t\ge h(1/\sum_t\eta_t)$, equality iff $x=x^{FB}(\eta)$
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ be such that $y\mapsto y\,h(y)$ is strictly convex on $[0,\infty)$. Let $\eta_1,\dots,\eta_T>0$ and let $x$ be a trading schedule ($x_t\ge0$, $\sum_t x_t=1$). Then
--
--   $$\sum_{t=1}^T h\!\left(\frac{x_t}{\eta_t}\right)x_t\;\ge\;h\!\left(\frac{1}{\sum_{t=1}^T\eta_t}\right),$$
--
--   with equality if and only if $x_t=\eta_t/\sum_{s=1}^T\eta_s$ for every $t$.
--
--   This is the deterministic core of Lemma 3: the left side is the impact part of the dealer's expected trading cost conditional on $\eta$, so the inequality and its equality case identify volume participation as the unique cost-minimizing schedule.
--
--   **Formalization Note** Stated for every number of periods $n$ and for any real function $h$ with the convexity property; no other assumption of the model is used. A schedule has $n\ge1$ automatically.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), p. 50 (PDF 51), proof of Lemma 3 (the Jensen display and the two sentences after it)

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem lemma_3_jensen
    (h : ℝ → ℝ) (hconv : StrictConvexOn ℝ (Set.Ici 0) (fun y => y * h y)) :
    ∀ (n : ℕ) (x e : Fin n → ℝ), IsSchedule x → (∀ t, 0 < e t) →
      h (1 / ∑ t, e t) ≤ ∑ t, h (x t / e t) * x t ∧
      (h (1 / ∑ t, e t) = ∑ t, h (x t / e t) * x t ↔ ∀ t, x t = xFB e t) := by sorry

end VWAPContract.Optimal
