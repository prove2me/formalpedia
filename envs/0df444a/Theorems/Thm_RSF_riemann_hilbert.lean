-- Prove2me | Theorems.Thm_RSF_riemann_hilbert
-- name    : RSF.riemann_hilbert
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-23T03:16:30.362993+00:00
-- url     : https://prove2.me/theorems/648ba23a-bcea-4b2a-a004-90c65a2b50d0
-- title:
--   A p-torsion Riemann-Hilbert correspondence (Theorem 1.2.7)
-- statement:
--   Theorem 1.2.7 of the thesis: on a small v-stack over Z_p with pseudouniformizer pi dividing p, the functor of tensoring an overconvergent etale F_p-sheaf with the structure sheaves O^+a/pi, which lands in phi-modules - modules with a Frobenius-semilinear structure whose Frobenius pullback is invertible - is fully faithful, and it induces an equivalence of the perfect objects on both sides: every perfect phi-module is the image of an etale sheaf, and the image of an etale sheaf is perfect. This correspondence carries the almost purity information that links the O^+/pi-cohomology of the six-functor formalism to the F_p-cohomology of the goal.
--
--   **Formalization Note** The Riemann-Hilbert world is abstract interface data; full faithfulness is the bijectivity of the action on hom-types, and the equivalence on perfect objects is encoded through the object-level image and the perfectness predicate.
-- source:
--   L. Mann, A p-Adic 6-Functor Formalism in Rigid-Analytic Geometry, arXiv:2206.02022 (2022), Theorem 1.2.7 (proved as Theorem 3.9.23).

import Mathlib
import Definitions.Def_RSF_cat
import Definitions.Def_RSF_geo

namespace RSF

/-!  Theorem 1.2.7 of the thesis: a p-torsion Riemann-Hilbert correspondence.
The functor of tensoring an overconvergent etale F_p-sheaf with the
structure sheaves O^+a/pi, landing in phi-modules, is fully faithful, and
it induces an equivalence of the perfect objects on both sides: every
perfect phi-module is the image of an etale sheaf, and the image of an
etale sheaf is perfect. This correspondence carries the information of
Faltings' almost purity that links the O^+/pi-cohomology of the six-functor
formalism to the F_p-cohomology of the goal.  -/

theorem riemann_hilbert : ∀ w : RHWorld,
    (∀ A B : w.Sheaf, Function.Bijective (w.Tmor A B)) ∧
    (∀ M : w.PhiMod, w.IsPerfect M → ∃ N : w.Sheaf, w.T N = M) ∧
    (∀ N : w.Sheaf, w.IsPerfect (w.T N)) := by
  sorry

end RSF
