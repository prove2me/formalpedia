-- Prove2me | Theorems.Thm_ProductFraming_Nest_theorem_2
-- name    : ProductFraming.Nest.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:31.199977+00:00
-- url     : https://prove2.me/theorems/1a6ff3f7-f3f4-455b-8c22-2ae67ff97d1d
-- title:
--   Theorem 2 — the clairvoyant bound $\mathbb E[U(X)] \ge V^{OPT}$
-- statement:
--   In the product framing model with $n$ products, $m\ge1$ pages of capacity $p\ge1$, revenues $r_i$, a choice model $P$ and a page-count law $\lambda$ on $[m]$, let $U(x)=G(x\cdot p)$ be the optimal revenue of an assortment of at most $x\cdot p$ products. Then the optimal expected revenue of problem (1) is at most the revenue of a seller who knows $X$ in advance:
--   $$V^{OPT}\ \le\ \mathbb E[U(X)]=\sum_{x\in[m]}\lambda(x)\,U(x).$$
--
--   This upper bound, which is easy to compute, is the benchmark against which the approximation ratios of the paper are proved.
--
--   **Formalization Note** No assumption beyond the model of §3 is used (no A1, A3, or sign condition on $r$).
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, p. 7, Theorem 2 (proof p. 34)

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model

namespace ProductFraming.Nest

open Finset

/-- Theorem 2 (Gallego, Li, Truong, Wang 2020, p. 7): the clairvoyant bound `E[U(X)] ≥ V^OPT`. -/
theorem theorem_2 (n m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (r : Fin n → ℝ)
    (P : Fin n → Finset (Fin n) → ℝ) (hP : IsChoiceModel P) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) :
    Vopt n m p r P lam ≤ ∑ x ∈ Icc 1 m, lam x * U p r P x := by sorry

end ProductFraming.Nest
