-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_groupObjectsInCatAreGroupoids
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.groupObjectsInCatAreGroupoids
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:34:57.613056+00:00
-- url     : https://prove2.me/theorems/a1d210a1-3965-4201-9823-d40879c7c51c
-- title:
--   Every strict group object in Cat is a groupoid
-- statement:
--   Let a small category have object group $O$ and total arrow group $A$, with multiplication, unit and group inversion defining a strict group object in Cat. Every arrow $f$ has a categorical inverse $g$ with
--
--   $$s(g)=t(f),\qquad t(g)=s(f),\qquad g\circ f=e(s(f)),\qquad f\circ g=e(t(f)).$$
--
--   Thus its underlying category is a groupoid, with the same strict group-object operations. Combining this fact with the two preceding structure correspondences identifies crossed modules with group objects in Grpd in the same structural sense used by the source.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 12, §3, Brown–Spencer strengthening

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF p. 12, the Brown-Spencer strengthening as explicitly stated in this
paper: every arrow of a strict group object in Cat has a two-sided categorical
inverse. This is categorical inversion, distinct from the ambient group inverse.
Together with the two structure correspondences above, this gives the stated
crossed-module correspondence with group objects in Grpd. The source supplies
no further hypothesis and does not require its cited proof as input. -/
theorem groupObjectsInCatAreGroupoids {A : Type u} {O : Type v}
    [Group A] [Group O] (D : CategoryMaps A O) (h : GroupObjectInCat D) :
    ∀ f : A, ∃ g : A,
      D.source g = D.target f ∧ D.target g = D.source f ∧
      D.compose g f = D.identity (D.source f) ∧
      D.compose f g = D.identity (D.target f) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
