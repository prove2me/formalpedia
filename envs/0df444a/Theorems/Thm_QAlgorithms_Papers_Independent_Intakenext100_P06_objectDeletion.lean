-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_objectDeletion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.objectDeletion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:49:12.991053+00:00
-- url     : https://prove2.me/theorems/dae03e92-9b1d-457d-8bc3-0fe4c005b33b
-- title:
--   Delete one isomorphic object and transport all Gr-data
-- statement:
--   Let $\mathcal C$ be a Gr-category, let $g\ne s$ be objects, and let $f:g\xrightarrow{\sim}s$. Let $\mathcal R$ be the full subcategory on the objects other than $g$, and define $r(g)=s$ and $r(x)=x$ for $x\ne g$. There is an equivalence $e:\mathcal C\simeq\mathcal R$ whose inverse is the actual inclusion, whose object map is $r$, and whose unit comparison is $f$ at $g$ and the identity elsewhere. Transporting the full monoidal structure along this specified equivalence gives
--
--   $$
--   x\otimes_{\mathcal R}y=r(x\otimes_{\mathcal C}y),\qquad
--   \mathcal C\simeq_{\otimes}\mathcal R,
--   $$
--
--   and makes $\mathcal R$ a Gr-category. The transports compute tensor on arrows, associator, unitors, and all equivalence comparison maps. The remaining objects need not be tensor-closed, and the old unit may itself be the deleted object.
--
--   This is the explicit removal construction underlying skeletal replacement.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 7, §3: remove an isomorphic object and reroute all Gr-data

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Section 3, PDF p. 7: delete one of two distinct isomorphic objects.
The inverse functor is the actual full-subcategory inclusion; the unit
is the given f at g and the identity elsewhere. Monoidal.transport
computes every tensor, associator, unitor, and comparison from this
ordinary equivalence; tensor-closure of the remaining objects is not assumed. -/
theorem objectDeletion {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (h : IsWeakTwoGroup C) (g survivor : C) (hne : g ≠ survivor)
    (f : g ≅ survivor) :
    ∃ e : C ≌ RemovedObjects g,
      e.inverse = ObjectProperty.ι (fun x : C => x ≠ g) ∧
      (∀ x : C, (e.functor.obj x).obj = redirectObject g survivor x) ∧
      (∀ x : C, ∃ p : e.inverse.obj (e.functor.obj x) = redirectObject g survivor x,
        e.unitIso.app x ≪≫ eqToIso p = redirectIso f x) ∧
      (letI := Monoidal.transport e
       IsWeakTwoGroup (RemovedObjects g) ∧
       (∀ x y : RemovedObjects g,
         (x ⊗ y).obj = redirectObject g survivor (x.obj ⊗ y.obj)) ∧
       ∃ E : GrEquivalence C (RemovedObjects g), E.e = e) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
