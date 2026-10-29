-- Prove2me | Theorems.Thm_PochetWolsey_Variants_sales_extreme_points
-- name    : PochetWolsey.Variants.sales_extreme_points
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:14.331829+00:00
-- url     : https://prove2.me/theorems/c1b76191-2505-4388-a1d3-261237853d33
-- title:
--   Proposition 11.3 — extreme points with sales
-- statement:
--   For the nonnegative-demand sales model with zero initial and final stock, let $(x,v,y)$ be an extreme point of the convex hull of its original feasible set. There are subsets $I\subseteq J$ and $H$ of the periods, with $I=\{t_1<\cdots<t_q\}$ and $t_{q+1}=n+1$, such that
--   $$y_t=\mathbf1_{t\in J},\qquad v_t=u_t\mathbf1_{t\in H},\qquad x_{t_j}=\sum_{i=t_j}^{t_{j+1}-1}(d_i+v_i),$$
--   and $x_t=0$ outside $I$.
--
--   This gives the regeneration structure used in the sales formulation. It asserts that every extreme point has such a description, not that every unconstrained choice of the three sets is feasible.
--
--   **Formalization Note** The book's third set $K$ is called $H$ to avoid confusion with production types. The last displayed clause uses the production period as its index; the source switches to the letter $j$ there. Empty $I$ is allowed when production is zero.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 338 (PDF 351), Proposition 11.3; DOI 10.1007/0-387-33477-7

import Definitions.Def_PochetWolsey_Variants_SalesModel

/- Imported module source, reproduced verbatim for declaration-only auditing.
import Mathlib

open scoped BigOperators

namespace PochetWolsey.Variants

abbrev SalesPoint (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)

structure SalesModel (n : ℕ) where
  d : Fin n → ℝ
  u : Fin n → ℝ
  M : ℝ

def SalesModel.Standing {n : ℕ} (D : SalesModel n) : Prop :=
  0 < n ∧ (∀ t, 0 ≤ D.d t ∧ 0 ≤ D.u t) ∧
  0 < D.M ∧ (∑ t, (D.d t + D.u t)) ≤ D.M

def SalesModel.feasible {n : ℕ} (D : SalesModel n) : Set (SalesPoint n) :=
  {w | (∀ t, 0 ≤ w.1 t ∧ 0 ≤ w.2.1 t ∧ w.2.1 t ≤ D.u t ∧
        (w.2.2 t = 0 ∨ w.2.2 t = 1) ∧ w.1 t ≤ D.M * w.2.2 t) ∧
    (∀ t, (∑ j ∈ Finset.univ.filter (fun j => j ≤ t), (w.2.1 j + D.d j)) ≤
      ∑ j ∈ Finset.univ.filter (fun j => j ≤ t), w.1 j) ∧
    (∑ j, w.1 j) = ∑ j, (w.2.1 j + D.d j)}

noncomputable def SalesModel.regenerationPattern {n : ℕ} (D : SalesModel n)
    (w : SalesPoint n) : Prop :=
  ∃ I J H : Finset (Fin n), I ⊆ J ∧
    (∀ t, w.2.2 t = if t ∈ J then 1 else 0) ∧
    (∀ t, w.2.1 t = if t ∈ H then D.u t else 0) ∧
    (∀ t, w.1 t = if t ∈ I then
      ∑ r ∈ Finset.univ.filter (fun r => t ≤ r ∧ ∀ j ∈ I, t < j → r < j),
        (w.2.1 r + D.d r) else 0)

end PochetWolsey.Variants
-/

namespace PochetWolsey.Variants

theorem sales_extreme_points {n : ℕ} (D : SalesModel n) (hD : D.Standing)
    (w : SalesPoint n) (hw : w ∈ (convexHull ℝ D.feasible).extremePoints ℝ) :
    D.regenerationPattern w := by sorry

end PochetWolsey.Variants
