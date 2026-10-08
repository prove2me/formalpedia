-- Prove2me | Theorems.Thm_ProductFraming_Trunc_theorem_4
-- name    : ProductFraming.Trunc.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:16:23.0145+00:00
-- url     : https://prove2.me/theorems/22b2b5e3-0a24-4f1c-a445-64dffd5dc8d8
-- title:
--   Theorem 4 — under B1, B2, B3, B4, $V^{TRUNC}\ge\frac13 V^{OPT}$
-- statement:
--   Consider the type-dependent product framing problem: $n$ products with revenues $r_i\ge 0$, $m\ge 1$ pages of capacity $p\ge 1$, a choice model $P_x$ for each consumer type $x\in[m]$ (a consumer of type $x$ views exactly $x$ pages), and a page-count law $\lambda$ on $[m]$. Assume
--
--   1. **B1**: $R_x(S)\le R_y(S)$ for all $1\le x\le y\le m$ and $|S|\le x\cdot p$;
--   2. **B2**: $U(x)/x$ is nonincreasing on $[m]$, where $U(x)=\max_{|S|\le xp}R_x(S)$;
--   3. **B3** (with $\epsilon=0$): the assortment problem (9) is solved exactly;
--   4. **B4**: $X$ has an increasing failure rate.
--
--   For each $y\in[m]$ let $(S(y),f_y)$ be any run of TRUNC($y$): an optimal assortment of (9) for type $y$, placed in any arrangement on pages $1,\dots,y$, with pages $y+1,\dots,m$ blank. Let $V^{TRUNC}=\max_{y\in[m]}V^{TRUNC(y)}$ be the revenue of the best of these framings. Then
--
--   $$V^{TRUNC}\;\ge\;\frac13\,V^{OPT}.$$
--
--   TRUNC solves only $m$ capacitated assortment problems, while computing $V^{OPT}$ is NP-hard (Theorem 1), so this is a constant-factor approximation guarantee for framing under type-dependent choice.
--
--   **Formalization Note** The bound holds for every family of TRUNC runs, i.e. for every choice of optimal assortments and every filling heuristic. B3 is built into the definition of a run. The hypothesis $r_i\ge 0$ is added (the paper speaks of unit profits or revenues). IFR is required only where the failure rate is defined ($\Lambda>0$).
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, p. 15, Theorem 4 (model §6, pp. 13–14; proof A.4, pp. 39–42)

import Mathlib
import Definitions.Def_ProductFraming_Trunc_Framing
import Definitions.Def_ProductFraming_Trunc_Model
open Finset

namespace ProductFraming.Trunc

theorem theorem_4 {n : ℕ} (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p)
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ)
    (hP : ∀ x ∈ Icc 1 m, ProductFraming.Nest.IsChoiceModel (Pt x)) (lam : ℕ → ℝ) (hlam : ProductFraming.Nest.IsPageLaw m lam)
    (hB1 : AssumptionB1 m p r Pt) (hB2 : AssumptionB2 m p r Pt) (hB4 : IsIFR m lam)
    (S : ℕ → Finset (Fin n)) (F : ℕ → Fin n → ℕ)
    (hrun : ∀ y ∈ Icc 1 m, IsTruncRun m p r Pt y (S y) (F y)) :
    (1 / 3 : ℝ) * VoptT m p lam r Pt ≤
      (Icc 1 m).sup' (nonempty_Icc.mpr hm) (fun y => Vt m lam r Pt (F y)) := by sorry

end ProductFraming.Trunc
