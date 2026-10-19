-- Prove2me | Theorems.Thm_RawBlending_UB_proposition_2
-- name    : RawBlending.UB.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:16.086051+00:00
-- url     : https://prove2.me/theorems/44f4ffc1-ca12-469c-b451-5600a71c44c6
-- title:
--   Proposition 2 (corrected partition): optimal solution and binding constraints
-- statement:
--   Let $J$ be convex, continuous, supermodular, and coercive in each material coordinate on $\mathbb R_+^2$, with $0<a^1<a^2$. There exist curves $\gamma^1,\gamma^2,\alpha,\beta$ with the meeting and minimization properties of equations (11)–(14) such that their six regions cover $\mathbb R_+^2$ for every demand $D\ge0$ and capacity $R\ge0$. The regions are pairwise disjoint when $a^1R<D$. For every inventory $y\in\mathbb R_+^2$, an optimum $w^*$ of $J$ over $E_2(y,D,R)$ exists. On $\mathcal R_0$ it equals the use-down-to point. Outside $\mathcal R_0$, constraint (4) binds when $D\le a^1R$; in the middle regime it binds on $\mathcal R_1\cup\mathcal R_2$, constraint (5) binds on $\mathcal R_4\cup\mathcal R_5$, and both bind on $\mathcal R_3$; when $D\ge a^2R$, constraint (5) binds.
--
--   $$
--   a^1w^{*1}+a^2w^{*2}=a^1y^1+a^2y^2-D\quad\text{for binding (4)},\qquad
--   w^{*1}+w^{*2}=y^1+y^2-R\quad\text{for binding (5)}.
--   $$
--
--   This records the limiting production geometry used in the main result.
--
--   **Formalization Note** The paper constructs particular curves through a limiting argument. The existential quantifier preserves that selection: the assertion is not about every arbitrary choice of minimizers in (11)–(14). The page calls the regions a partition without a regime restriction, but they overlap when $D\le a^1R$; the corrected statement retains coverage everywhere and asserts pairwise disjointness only for $a^1R<D$.
-- source:
--   Chen, Duenyas & Jasin, Optimal use and replenishment of two substitutable raw materials, SSRN working paper 2801786 (version of 2016-06-28), p. 22 (PDF 22), Proposition 2; corrected partition claim

import Mathlib
import Definitions.Def_RawBlending_UB_Policy

namespace RawBlending.UB

theorem proposition_2 (Jobj : Vec → ℝ) (hJ : IsJClass Jobj)
    (a1 a2 : ℝ) (ha1 : 0 < a1) (ha2 : a1 < a2) :
    ∃ C : Curves, IsUBCurves Jobj a1 a2 C ∧
      ∀ D R : ℝ, 0 ≤ D → 0 ≤ R →
      RegionsCover C a1 a2 D R ∧
      (a1 * R < D → RegionsDisjoint C a1 a2 D R) ∧
      ∀ y : Vec, y ∈ orthant →
        ∃ w : Vec, Minimizes Jobj (E2 a1 a2 y D R) w ∧
          (y ∈ R0 C a1 a2 D R →
            w = (min y.1 (max (C.γ1 y.2) C.wbar.1),
                 min y.2 (max (C.γ2 y.1) C.wbar.2))) ∧
          (y ∉ R0 C a1 a2 D R →
            (D ≤ a1 * R →
              a1 * w.1 + a2 * w.2 = a1 * y.1 + a2 * y.2 - D) ∧
            (a1 * R < D → D < a2 * R →
              ((y ∈ R1 C a1 a2 D R ∨ y ∈ R2 C a1 a2 D R) →
                a1 * w.1 + a2 * w.2 = a1 * y.1 + a2 * y.2 - D) ∧
              ((y ∈ R4 C a1 a2 D R ∨ y ∈ R5 C a1 a2 D R) →
                w.1 + w.2 = y.1 + y.2 - R) ∧
              (y ∈ R3 C a1 a2 D R →
                a1 * w.1 + a2 * w.2 = a1 * y.1 + a2 * y.2 - D ∧
                w.1 + w.2 = y.1 + y.2 - R)) ∧
            (a2 * R ≤ D → w.1 + w.2 = y.1 + y.2 - R)) := by sorry

end RawBlending.UB
