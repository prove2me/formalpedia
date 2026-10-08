-- Prove2me | Theorems.Thm_ProductFraming_Nest_theorem_3
-- name    : ProductFraming.Nest.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:48.234993+00:00
-- url     : https://prove2.me/theorems/b8d09872-ebcb-47a6-b834-a0c137a8b0d3
-- title:
--   Theorem 3 — $V^{NEST} \ge (6/\pi^2)\, V^{OPT}$
-- statement:
--   Consider the product framing problem with $n$ products, $m\ge1$ pages of capacity $p\ge1$, nonnegative revenues $r_i$, a choice model $P$ satisfying Assumption A1, and a page-count law $\lambda$ on $[m]$ that is NBUE (Assumption A3). For each $y\in[m]$ let $S_y(1),\dots,S_y(y)$ be any run of NEST($y$) (with an exact solution of problem (2), i.e. A2 with $\varepsilon=0$), and let $V^{NEST}=\max_{y\in[m]}V^{NEST(y)}$ be the best expected revenue among the framings these runs display. Then
--   $$V^{NEST}\ \ge\ \frac{6}{\pi^2}\,V^{OPT}.$$
--
--   This is the main result of the paper on product framing: NEST earns at least $6/\pi^2\approx0.608$ of the optimal expected revenue, although problem (1) is NP-hard.
--
--   **Formalization Note** The guarantee is stated for every choice of the runs, since the algorithm's choices are arbitrary; that runs exist is a separate milestone. The hypothesis $r_i\ge0$ is added (unit revenues; Lemmas 1 and 2 need it). A2 is used with $\varepsilon=0$, as in the paper; with $\varepsilon>0$ the paper states that the bound scales by $(1-\varepsilon)$, which is not formalized. Pages are 1-based and "not displayed" is page $0$.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, p. 10, Theorem 3 (proof pp. 37–38)

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
import Definitions.Def_ProductFraming_Nest_Algorithm

namespace ProductFraming.Nest

open Finset

/-- Theorem 3 (Gallego, Li, Truong, Wang 2020, p. 10): under A1, A2 with `ε = 0` and A3,
`V^{NEST} ≥ (6/π²) V^{OPT}`, for every choice of the NEST(y) runs `runs y`, `y ∈ [m]`. The
hypothesis `0 ≤ r` is added. -/
theorem theorem_3 (n m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (P : Fin n → Finset (Fin n) → ℝ) (hP : IsChoiceModel P) (hA1 : SatisfiesA1 P)
    (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam)
    (runs : ℕ → ℕ → Finset (Fin n)) (hruns : ∀ y ∈ Icc 1 m, IsNestRun p r P y (runs y)) :
    6 / Real.pi ^ 2 * Vopt n m p r P lam ≤ VNEST hm r P lam runs := by sorry

end ProductFraming.Nest
