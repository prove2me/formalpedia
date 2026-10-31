-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P59_cfg_pullbacks_unique_and_fibers_groupoids
-- name    : QAlgorithms.Papers.Independent.Intake100.P59.cfg_pullbacks_unique_and_fibers_groupoids
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:05:17.099182+00:00
-- url     : https://prove2.me/theorems/8bbe6296-6c86-4f9a-b9bd-9248fd5bfed1
-- title:
--   Unique compatible pullback isomorphisms and groupoid fibers
-- statement:
--   Let $p:D\to C$ be a category fibered in groupoids, in the sense of Definition 4.2. Write $D(X)$ for its fiber over $X$, whose arrows project to $\mathrm{id}_X$. Let $f:Y\to X$, $\xi\in D(X)$ and $\xi_1,\xi_2\in D(Y)$, and let $h_i:\xi_i\to\xi$ project to $f$. There is exactly one isomorphism $k:\xi_1\to\xi_2$ in $D(Y)$ with
--
--   $$
--   h_2\circ k=h_1,\qquad h_1\circ k^{-1}=h_2.
--   $$
--
--   Moreover every arrow of every fiber $D(X)$ is invertible. This identifies pullbacks only through their compatible vertical isomorphism; it does not claim that all isomorphisms between their sources are unique.
-- source:
--   Orbifolds as stacks?, arXiv:0806.4160v2, PDF p. 19, remarks4.6-4.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P59

namespace QAlgorithms.Papers.Independent.Intake100.P59

open CategoryTheory

universe u v uC vC uD vD uE vE

/-- Remarks 4.6–4.7, PDF p.19: two lifts of the same base arrow have a unique
compatible vertical isomorphism, and every arrow of a fiber is invertible.
The compatibility requirement is part of the uniqueness assertion. -/
theorem cfg_pullbacks_unique_and_fibers_groupoids
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    (p : D ⥤ C) (hp : IsCFG p) :
    (∀ {Y X : C} (f : Y ⟶ X) (x : p.Fiber X) (y1 y2 : p.Fiber Y)
      (h1 : y1.1 ⟶ x.1) (h2 : y2.1 ⟶ x.1),
      p.IsHomLift f h1 → p.IsHomLift f h2 →
        ∃! e : y1 ≅ y2, e.hom.1 ≫ h2 = h1 ∧ e.inv.1 ≫ h1 = h2) ∧
    (∀ (X : C) (x y : p.Fiber X) (f : x ⟶ y), IsIso f) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P59
