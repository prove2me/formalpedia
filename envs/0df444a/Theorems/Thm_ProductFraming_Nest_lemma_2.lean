-- Prove2me | Theorems.Thm_ProductFraming_Nest_lemma_2
-- name    : ProductFraming.Nest.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:08.683188+00:00
-- url     : https://prove2.me/theorems/5dfaf647-bccc-48a8-8ee9-38c81563d3d7
-- title:
--   Lemma 2 — $U(x)/x$ is decreasing in $x$
-- statement:
--   Let $P$ be a choice model satisfying Assumption A1, let $r_i\ge0$ and $m,p\ge1$, and let $U(x)=G(x\cdot p)$ be the optimal revenue of an assortment of at most $x\cdot p$ products. Then $U(x)/x$ is decreasing on $[m]$: for all $x\le x'$ in $[m]$,
--   $$\frac{U(x')}{x'}\ \le\ \frac{U(x)}{x}.$$
--
--   The paper cites this from Davis, Topaloglu and Williamson (2015). It is the page-level version of Lemma 1 and the fourth constraint of the bound-revealing program (5).
--
--   **Formalization Note** "Decreasing" is read as nonincreasing, as the constraint $U(x)/x\ge U(x+1)/(x+1)$ of (5) shows. The hypothesis $r_i\ge0$ is added.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, p. 8, Lemma 2 (Davis et al. 2015)

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model

namespace ProductFraming.Nest

open Finset

/-- Lemma 2 (Davis et al. 2015; Gallego, Li, Truong, Wang 2020, p. 8): `U(x)/x` is (weakly)
decreasing in `x ∈ [m]`. The hypothesis `0 ≤ r` is added. -/
theorem lemma_2 (n m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (P : Fin n → Finset (Fin n) → ℝ) (hP : IsChoiceModel P) (hA1 : SatisfiesA1 P) :
    ∀ x ∈ Icc 1 m, ∀ x' ∈ Icc 1 m, x ≤ x' →
      U p r P x' / (x' : ℝ) ≤ U p r P x / (x : ℝ) := by sorry

end ProductFraming.Nest
