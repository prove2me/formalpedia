-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_charOf_eq_fb1e6fa2063a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Conservation_charOf_eq_fb1e6fa2063a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:19.687813+00:00
-- url     : https://prove2.me/theorems/832d587e-74d1-44bd-a5c0-387ebc971a65
-- title:
--   P2 M Ground Theory Heights  Heights Inter Conservation char Of eq fb1e6fa2063a: P2 M Ground Theory Heights  Heights Inter Conservation char Of eq fb1e6fa2063a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Conservation char Of eq fb1e6fa2063a construction uses the P2 M Ground Theory Heights  Heights Inter Conservation char Of eq fb1e6fa2063a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L72-L80

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Conservation_charOf_eq_fb1e6fa2063a {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    charOf W = p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Conservation».«charOf_eq» := P2M_GroundTheory_Heights__Heights_Inter_Conservation_charOf_eq_fb1e6fa2063a
