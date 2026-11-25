-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_De_swap_7dbab2474d2c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_De_swap_7dbab2474d2c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:01.016806+00:00
-- url     : https://prove2.me/theorems/2b3e3e71-07d9-4f48-9c34-ad4d97afafed
-- title:
--   P2 M Ground Theory Heights  Heights Inter De swap 7dbab2474d2c: P2 M Ground Theory Heights  Heights Inter De swap 7dbab2474d2c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter De swap 7dbab2474d2c construction uses the P2 M Ground Theory Heights  Heights Inter De swap 7dbab2474d2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NoCommonComponentCoordinatesPlane.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NoCommonComponentCoordinatesPlane.lean#L29-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_De_swap_7dbab2474d2c (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι)
    (s s' : MRing ι) : De P L A' A s' s = -De P L A A' s s' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«De_swap» := P2M_GroundTheory_Heights__Heights_Inter_De_swap_7dbab2474d2c
