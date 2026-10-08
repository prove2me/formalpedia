-- Prove2me | Theorems.Thm_ProductFraming_Trunc_theorem_2_type_dependent
-- name    : ProductFraming.Trunc.theorem_2_type_dependent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:16:18.088689+00:00
-- url     : https://prove2.me/theorems/791451b9-2cd8-4ea9-a1d8-8fd8bd3eb9d6
-- title:
--   §6 — Theorem 2 remains valid for type-dependent choice: $\mathbf E[U(X)]\ge V^{OPT}$
-- statement:
--   Consider the type-dependent framing model with $m\ge 1$ pages of capacity $p\ge 1$, revenues $r_i$, a choice model $P_x$ for each type $x\in[m]$, and a page-count law $\lambda$ on $[m]$. Let $U(x)=\max_{|S|\le x p}R_x(S)$ be the optimal value of the capacitated assortment problem (9) for type $x$. Then the optimal expected framing revenue is at most the clairvoyant bound:
--
--   $$V^{OPT}\le\mathbf E[U(X)]=\sum_{x\in[m]}\lambda(x)\,U(x).$$
--
--   This is the upper bound against which the TRUNC algorithm is measured; it says that knowing each consumer's type in advance can only help.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, §6, p. 13 (Theorem 2 of p. 7 with P replaced by P_x; proof A.1, p. 34)

import Mathlib
import Definitions.Def_ProductFraming_Trunc_Framing
import Definitions.Def_ProductFraming_Trunc_Model
open Finset

namespace ProductFraming.Trunc

theorem theorem_2_type_dependent {n : ℕ} (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p)
    (r : Fin n → ℝ) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ)
    (hP : ∀ x ∈ Icc 1 m, ProductFraming.Nest.IsChoiceModel (Pt x)) (lam : ℕ → ℝ) (hlam : ProductFraming.Nest.IsPageLaw m lam) :
    VoptT m p lam r Pt ≤ ∑ x ∈ Icc 1 m, lam x * Ut p r Pt x := by sorry

end ProductFraming.Trunc
