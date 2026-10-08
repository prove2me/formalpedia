-- Prove2me | Theorems.Thm_SPHardness_FixedRecourse_lemma_1
-- name    : SPHardness.FixedRecourse.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:48.667316+00:00
-- url     : https://prove2.me/theorems/75cd291f-468f-442a-8ae5-da190aeb16d3
-- title:
--   Lemma 1, proof, (6), p. 5 — volume errors recover the #Parity count
-- statement:
--   Let $\alpha\in\mathbb N^k$ have positive coordinates, $0\le\beta\le\sum_j\alpha_j$, and $0\le\varepsilon$ satisfy the strict threshold (3). Suppose approximations $g_{\varepsilon,i}$ obey $|g_{\varepsilon,i}-V(\alpha,\gamma_i)|\le\varepsilon$ for every $i$. If $x^*$ and $x^*_{\varepsilon}$ solve the exact and perturbed systems (5), respectively, then
--   $$\|x^*_{\varepsilon}-x^*\|_1<\tfrac12,\qquad |x^*_{\varepsilon,0}-D|<\tfrac12.$$
--   Thus the first approximate coefficient determines the exact #Parity count by nearest-integer rounding. This is the numerical correctness claim inside Lemma 1.
--
--   **Formalization Note** Positive weights keep the threshold denominator meaningful; the paper reduces zero weights away implicitly.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), pp. 4–6, Lemma 1, (3), (5) and (6)

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SPHardness.FixedRecourse

theorem lemma_1 {k : ℕ} (α : Fin k → ℕ) (hα : ∀ j, 1 ≤ α j)
    (β : ℕ) (hβ : β ≤ ∑ j, α j) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε < eps3 (fun j => (α j : ℝ)))
    (gε : Fin (k + 1) → ℝ)
    (hgε : ∀ i, |gε i - vol (fun j => (α j : ℝ))
      (budget k (β : ℝ) i)| ≤ ε)
    (xstar xε : Fin (k + 1) → ℝ)
    (hxstar : (vandermondeF k (β : ℝ)).mulVec xstar =
      ((k.factorial : ℝ) * ∏ j, (α j : ℝ)) •
        (fun i => vol (fun j => (α j : ℝ)) (budget k (β : ℝ) i)))
    (hxε : (vandermondeF k (β : ℝ)).mulVec xε =
      ((k.factorial : ℝ) * ∏ j, (α j : ℝ)) • gε) :
    (∑ c, |xε c - xstar c|) < (1 / 2 : ℝ) ∧
      |xε 0 - (parityD α β : ℝ)| < (1 / 2 : ℝ) := by sorry
end SPHardness.FixedRecourse
