-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_vertR_C_prime_81226bff0cf2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Conservation_vertR_C_prime_81226bff0cf2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:27.621565+00:00
-- url     : https://prove2.me/theorems/3251828f-0f76-466d-8672-110c55d86721
-- title:
--   P2 M Ground Theory Heights  Heights Inter Conservation vert R C prime 81226bff0cf2: P2 M Ground Theory Heights  Heights Inter Conservation vert R C prime 81226bff0cf2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Conservation vert R C prime 81226bff0cf2 construction uses the P2 M Ground Theory Heights  Heights Inter Conservation vert R C prime 81226bff0cf2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ConservationDegreeFormOfExistence.lean#L82-L90

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Conservation_vertR_C_prime_81226bff0cf2 (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) {p : ℕ} (hp : p.Prime) :
    vertR P L (C (p : ℤ)) = Real.log p * ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
      (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (fun j => (L j).a) : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Conservation».«vertR_C_prime» := P2M_GroundTheory_Heights__Heights_Inter_Conservation_vertR_C_prime_81226bff0cf2
