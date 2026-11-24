-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_comap_eq_of_mem_03b704367dba
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Conservation_comap_eq_of_mem_03b704367dba
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:27.48163+00:00
-- url     : https://prove2.me/theorems/4f68f316-b742-41de-91b9-a34a72508564
-- title:
--   P2 M Ground Theory Heights  Heights Inter Conservation comap eq of mem 03b704367dba: P2 M Ground Theory Heights  Heights Inter Conservation comap eq of mem 03b704367dba
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Conservation comap eq of mem 03b704367dba construction uses the P2 M Ground Theory Heights  Heights Inter Conservation comap eq of mem 03b704367dba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L52-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.Conservation
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_Conservation_comap_eq_of_mem_03b704367dba {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    W.comap (C : ℤ →+* MRing ι) = Ideal.span {(p : ℤ)} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Conservation».«comap_eq_of_mem» := P2M_GroundTheory_Heights__Heights_Inter_Conservation_comap_eq_of_mem_03b704367dba
