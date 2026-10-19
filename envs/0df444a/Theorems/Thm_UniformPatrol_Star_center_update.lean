-- Prove2me | Theorems.Thm_UniformPatrol_Star_center_update
-- name    : UniformPatrol.Star.center_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:50.558736+00:00
-- url     : https://prove2.me/theorems/3520d8eb-00ee-4291-8d72-fb9f8ec6de4d
-- title:
--   Equations (3) and (15) — conditional centre update
-- statement:
--   Write $r=1-np$ and let $c(d)$ be the conditional probability of being at the centre at attack start with delay $d$. The update from one period of absence to the next is
--
--   $$c(d+1)=f(c(d),s),\qquad f(c,s)=\frac{cr+(1-c)s}{1-pc},\qquad c(2)=\frac{1-np}{1-p}.$$
--
--   When $s=1$, delay two minimizes $c(d)$ among all positive delays. The minimum is strict for every $d\ne2$ if $np<1$. This update controls how waiting changes the attack-start distribution.
--
--   **Formalization Note** The strict clause adds the positive-holding condition needed to exclude periodic ties at $np=1$. The mission assumes $n\geq2$.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 4 (PDF 5), eq. (3); p. 10 (PDF 11), eq. (15)

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model

namespace UniformPatrol.Star

/-- Equations (3) and (15): the centre update and its minimum at delay two when s = 1. -/
theorem center_update (n : ℕ) (hn : 2 ≤ n) (x : PStrat n) (A : Fin n) :
    (∀ d : ℕ, 1 ≤ d → cAt n x.p x.s A (d + 1) =
      fMap n x.p x.s (cAt n x.p x.s A d)) ∧
    cAt n x.p x.s A 2 =
      (1 - (n : ℝ) * x.p) / (1 - x.p) ∧
    (x.s = 1 → ∀ d : ℕ, 1 ≤ d →
      cAt n x.p x.s A 2 ≤ cAt n x.p x.s A d) ∧
    (x.s = 1 → (n : ℝ) * x.p < 1 → ∀ d : ℕ, 1 ≤ d → d ≠ 2 →
      cAt n x.p x.s A 2 < cAt n x.p x.s A d) := by sorry

end UniformPatrol.Star
