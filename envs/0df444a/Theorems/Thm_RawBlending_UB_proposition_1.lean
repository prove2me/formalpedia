-- Prove2me | Theorems.Thm_RawBlending_UB_proposition_1
-- name    : RawBlending.UB.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:13.062896+00:00
-- url     : https://prove2.me/theorems/405bc796-de38-4048-b375-a6a229c046e9
-- title:
--   Proposition 1: optimal UB policy for the strictly convex perturbation
-- statement:
--   Let $J^{(n)}(w)=J(w)+n^{-1}((w^1)^2+(w^2)^2)$ for an integer $n>0$, where $J$ has the convexity, continuity, supermodularity, and coordinatewise coercivity established for $J_t$ in Lemma 3(a). There exist the four argmin curves of page 20, meeting at a common point, whose UB rule is the unique optimum of the perturbed production problem for every $D,R\ge0$ and $y\in\mathbb R_+^2$:
--   $$
--    w^*(y,D,R)=\operatorname*{arg\,min}_{w\in E_2(y,D,R)}J^{(n)}(w).
--   $$
--   This is the perturbed policy milestone used before passage to the unperturbed objective.
--
--   **Formalization Note** The theorem abstracts $J_t$ by exactly the properties of Lemma 3(a). The paper’s $n\in\mathbb Z_{++}$ is represented by a positive natural number. The rule takes the first matching region when low-demand regions overlap.
-- source:
--   Chen, Duenyas & Jasin, Optimal use and replenishment of two substitutable raw materials, SSRN working paper 2801786 (version of 2016-06-28), p. 21 (PDF 21), Proposition 1; perturbation and argmin curves on p. 20 (PDF 20)

import Mathlib
import Definitions.Def_RawBlending_UB_Policy

namespace RawBlending.UB

theorem proposition_1 (Jobj : Vec → ℝ) (hJ : IsJClass Jobj)
    (a1 a2 : ℝ) (ha1 : 0 < a1) (ha2 : a1 < a2) (n : ℕ) (hn : 0 < n) :
    ∃ C : Curves, IsUBCurves (Jn Jobj n) a1 a2 C ∧
      ∀ D R : ℝ, 0 ≤ D → 0 ≤ R →
        RegionsCover C a1 a2 D R ∧
        ∀ y : Vec, y ∈ orthant →
          Minimizes (Jn Jobj n) (E2 a1 a2 y D R) (ubAction C a1 a2 D R y) ∧
          ∀ w : Vec, Minimizes (Jn Jobj n) (E2 a1 a2 y D R) w →
            w = ubAction C a1 a2 D R y := by sorry

end RawBlending.UB
