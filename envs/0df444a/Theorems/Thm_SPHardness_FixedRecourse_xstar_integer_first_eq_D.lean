-- Prove2me | Theorems.Thm_SPHardness_FixedRecourse_xstar_integer_first_eq_D
-- name    : SPHardness.FixedRecourse.xstar_integer_first_eq_D
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:37.519581+00:00
-- url     : https://prove2.me/theorems/0c23b18a-68b5-44b1-8427-e786a34731cf
-- title:
--   Proof of Lemma 1, p. 5 — integral coefficient vector and #Parity count
-- statement:
--   Let $\alpha\in\mathbb N^k$ have positive coordinates and let $\beta\in\mathbb N$. Put $g_i=V(\alpha,\gamma_i)$ for the $k+1$ budgets $\gamma_i=\beta+i/(k+1)$. Every solution $x^*$ of
--   $$Fx^*=\left(k!\prod_{j=1}^k\alpha_j\right)g$$
--   has integer coordinates, and its first coordinate is $D$, the feasible even-minus-odd #Parity count.
--
--   This identifies the integer that Lemma 1 recovers by rounding an approximate solution. The separately stated nonsingularity of $F$ ensures the solution exists and is unique.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 5, proof of Lemma 1 after (4)

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SPHardness.FixedRecourse

theorem xstar_integer_first_eq_D {k : ℕ} (α : Fin k → ℕ)
    (hα : ∀ j, 1 ≤ α j) (β : ℕ) (x : Fin (k + 1) → ℝ)
    (hx : (vandermondeF k (β : ℝ)).mulVec x =
      ((k.factorial : ℝ) * ∏ j, (α j : ℝ)) •
        (fun i => vol (fun j => (α j : ℝ)) (budget k (β : ℝ) i))) :
    x 0 = (parityD α β : ℝ) ∧ ∀ c, ∃ z : ℤ, x c = (z : ℝ) := by sorry
end SPHardness.FixedRecourse
