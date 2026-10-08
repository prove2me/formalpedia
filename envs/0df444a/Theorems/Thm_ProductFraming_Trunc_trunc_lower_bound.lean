-- Prove2me | Theorems.Thm_ProductFraming_Trunc_trunc_lower_bound
-- name    : ProductFraming.Trunc.trunc_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:18:03.117732+00:00
-- url     : https://prove2.me/theorems/ed200362-a2fe-45d4-8d70-ed0d7e358323
-- title:
--   §6.1 — $V^{TRUNC(y)}\ge U(y)\Lambda(y)$ under Assumption B1
-- statement:
--   In the type-dependent framing model with $m\ge 1$, $p\ge 1$, nonnegative revenues $r_i\ge 0$, a choice model $P_x$ for each type $x\in[m]$, a page-count law $\lambda$ with tail $\Lambda(x)=\mathbb P[X\ge x]$, and Assumption B1, every run of TRUNC($y$), $y\in[m]$, with chosen assortment $S(y)$ and framing $f$ earns at least
--
--   $$V^{TRUNC(y)}=\sum_{x\in[m]}\lambda(x)R_x(C_f(x))\;\ge\;U(y)\,\Lambda(y).$$
--
--   Every consumer who views $x\ge y$ pages sees all of $S(y)$; the bound credits only these consumers. Combined with the upper bound $\mathbf E[U(X)]\ge V^{OPT}$, it reduces Theorem 4 to the bound-revealing program (10).
--
--   **Formalization Note** The hypothesis $r_i\ge 0$ is added: the bound ignores the revenue of consumers who view fewer than $y$ pages, which requires that revenue to be nonnegative. The paper speaks of unit profits or revenues and uses $U\ge 0$ throughout.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, §6.1, p. 14

import Mathlib
import Definitions.Def_ProductFraming_Trunc_Framing
import Definitions.Def_ProductFraming_Trunc_Model
open Finset

namespace ProductFraming.Trunc

theorem trunc_lower_bound {n : ℕ} (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p)
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ)
    (hP : ∀ x ∈ Icc 1 m, ProductFraming.Nest.IsChoiceModel (Pt x)) (lam : ℕ → ℝ) (hlam : ProductFraming.Nest.IsPageLaw m lam)
    (hB1 : AssumptionB1 m p r Pt) :
    ∀ y ∈ Icc 1 m, ∀ (S : Finset (Fin n)) (f : Fin n → ℕ), IsTruncRun m p r Pt y S f →
      Ut p r Pt y * ProductFraming.Nest.tail m lam y ≤ Vt m lam r Pt f := by sorry

end ProductFraming.Trunc
