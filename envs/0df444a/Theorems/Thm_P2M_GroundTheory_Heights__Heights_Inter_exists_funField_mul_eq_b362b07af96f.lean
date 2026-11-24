-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exists_funField_mul_eq_b362b07af96f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_exists_funField_mul_eq_b362b07af96f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:00.514682+00:00
-- url     : https://prove2.me/theorems/226c9b7b-281d-4682-8a38-7dd7bcc42d0a
-- title:
--   P2 M Ground Theory Heights  Heights Inter exists fun Field mul eq b362b07af96f: P2 M Ground Theory Heights  Heights Inter exists fun Field mul eq b362b07af96f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter exists fun Field mul eq b362b07af96f construction uses the P2 M Ground Theory Heights  Heights Inter exists fun Field mul eq b362b07af96f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsFunFieldMulEq.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsFunFieldMulEq.lean#L18-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SameOrbitOneSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_exists_funField_mul_eq_b362b07af96f {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} [P.IsPrime] {f g : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) (hgP : g ∉ P) :
    ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«exists_funField_mul_eq» := P2M_GroundTheory_Heights__Heights_Inter_exists_funField_mul_eq_b362b07af96f
