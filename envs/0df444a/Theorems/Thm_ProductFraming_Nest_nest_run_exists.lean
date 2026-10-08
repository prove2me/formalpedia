-- Prove2me | Theorems.Thm_ProductFraming_Nest_nest_run_exists
-- name    : ProductFraming.Nest.nest_run_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:17.131858+00:00
-- url     : https://prove2.me/theorems/0f416a9a-c16f-4c52-ad30-44913c7e86db
-- title:
--   §4.2, NEST(y) step 2 — a run of NEST(y) always exists
-- statement:
--   Let $P$ be a choice model satisfying Assumption A1, let $r_i\ge0$, and let $m,p\ge1$. For every $y\in[m]$ there are sets $S(1),\dots,S(y)\subseteq[n]$ forming a run of NEST($y$): $S(y)$ is an optimal solution of problem (2) with bound $y\cdot p$, and for $x=y-1,\dots,1$,
--   $$S(x)\subseteq S(x+1),\qquad |S(x)|=\min(|S(x+1)|,\,x\cdot p),\qquad \frac{R(S(x))}{|S(x)|}\ge\frac{R(S(x+1))}{|S(x+1)|}.$$
--
--   The paper asserts this right after the description of the algorithm ("Lemma 1 ensures that we can always find such a set $S(x)$"). It shows that the guarantee of Theorem 3, which is stated for every run, is not about an empty set of runs.
--
--   **Formalization Note** The hypothesis $r_i\ge0$ is added, as for Lemma 1.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, §4.2, NEST(y) step 2, p. 9

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
import Definitions.Def_ProductFraming_Nest_Algorithm

namespace ProductFraming.Nest

open Finset

/-- §4.2, NEST(y) step 2, p. 9 (Gallego, Li, Truong, Wang 2020): "Lemma 1 ensures that we can always
find such a set S(x)." Every NEST(y), `y ∈ [m]`, has a run. The hypothesis `0 ≤ r` is added. -/
theorem nest_run_exists (n m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (P : Fin n → Finset (Fin n) → ℝ) (hP : IsChoiceModel P) (hA1 : SatisfiesA1 P) :
    ∀ y ∈ Icc 1 m, ∃ S : ℕ → Finset (Fin n), IsNestRun p r P y S := by sorry

end ProductFraming.Nest
