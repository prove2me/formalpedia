-- Prove2me | Theorems.Thm_RawBlending_UB_theorem_1
-- name    : RawBlending.UB.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:22.173005+00:00
-- url     : https://prove2.me/theorems/74294b3f-f801-43cc-bc36-feb2cfac7c0c
-- title:
--   Theorem 1: an optimal use-down-to/balancing policy
-- statement:
--   For every period $t=1,\ldots,T$ of the two-material dynamic program, there exist nonincreasing switching curves $\gamma_t^1,\gamma_t^2$ and balancing curves $\alpha_t,\beta_t$ meeting at $\bar w_t\in\mathbb R_+^2$. Their UB policy yields a feasible optimum for every nonnegative demand $D$, capacity $R$, and inventory $y$:
--   $$
--    w_t^*(y,D,R)\in\operatorname*{arg\,min}_{w\in E_2(y,D,R)}J_t(w).
--   $$
--   The common point minimizes $J_t$ on $\mathbb R_+^2$; each $\gamma_t^j$ minimizes its one-coordinate section; and $\alpha_t(x)$ and $\beta_t(x)$ minimize $J_t$ on the weighted-sum and sum level sets, respectively, for every $x\ge0$. These are all the additional claims of Theorem 1.
--
--   **Formalization Note** $J_t$ is computed from the paper’s full backward dynamic program. The region rule is applied in printed order where the low-demand regions overlap; coverage holds everywhere and disjointness is asserted only for $a^1R<D$. The cost-sign assumptions needed in Lemma 3 are explicit in `Standing`.
-- source:
--   Chen, Duenyas & Jasin, Optimal use and replenishment of two substitutable raw materials, SSRN working paper 2801786 (version of 2016-06-28), pp. 15–16 (PDF 15–16), Theorem 1

import Mathlib
import Definitions.Def_RawBlending_UB_Policy

namespace RawBlending.UB

theorem theorem_1 (d : Data) (hd : d.Standing) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ d.T) :
    ∃ C : Curves, IsUBCurves (J d t) d.a1 d.a2 C ∧
      ∀ D R : ℝ, 0 ≤ D → 0 ≤ R →
        RegionsCover C d.a1 d.a2 D R ∧
        (d.a1 * R < D → RegionsDisjoint C d.a1 d.a2 D R) ∧
        ∀ y : Vec, y ∈ orthant →
          Minimizes (J d t) (E2 d.a1 d.a2 y D R)
            (ubAction C d.a1 d.a2 D R y) := by sorry

end RawBlending.UB
