-- Prove2me | Theorems.Thm_ProductFraming_Nest_proposition_1
-- name    : ProductFraming.Nest.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:24.690711+00:00
-- url     : https://prove2.me/theorems/08739ad9-c028-4bd5-b57b-5875940baab2
-- title:
--   Proposition 1 — $V^{NEST(y)} \ge (U(y)/y)\,\mathbb E[\min(X,y)]$
-- statement:
--   In the product framing model with $m,p\ge1$, a choice model $P$ and a page-count law $\lambda$ on $[m]$, let $y\in[m]$ and let $S(1),\dots,S(y)$ be any run of NEST($y$). Then the expected revenue of the framing the run displays satisfies
--   $$V^{NEST(y)}\ \ge\ \frac{U(y)}{y}\,\mathbb E[\min(X,y)].$$
--
--   Taking the best $y$ gives $V^{NEST}\ge\max_{y\in[m]}\frac{U(y)}{y}\mathbb E[\min(X,y)]$, the lower bound that is compared with Theorem 2.
--
--   **Formalization Note** The statement holds for every run, and needs neither A1, A3 nor a sign condition on $r$. $\mathbb E[\min(X,y)]=\sum_{x\in[m]}\lambda(x)\min(x,y)$.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, p. 9, Proposition 1 (proof pp. 34–35)

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
import Definitions.Def_ProductFraming_Nest_Algorithm

namespace ProductFraming.Nest

open Finset

/-- Proposition 1 (Gallego, Li, Truong, Wang 2020, p. 9):
`V^{NEST(y)} ≥ (U(y)/y) E[min(X, y)]` for all `y ∈ [m]` and every run of NEST(y). -/
theorem proposition_1 (n m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (r : Fin n → ℝ)
    (P : Fin n → Finset (Fin n) → ℝ) (hP : IsChoiceModel P) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) :
    ∀ y ∈ Icc 1 m, ∀ S : ℕ → Finset (Fin n), IsNestRun p r P y S →
      U p r P y / (y : ℝ) * Emin m lam (y : ℝ) ≤ VNest m r P lam y S := by sorry

end ProductFraming.Nest
