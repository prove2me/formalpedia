-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_blocks_ne_zero_restrict_c2698d5c05ab
-- name    : P2M_GroundTheory_Heights__Heights_Inter_blocks_ne_zero_restrict_c2698d5c05ab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:34.183574+00:00
-- url     : https://prove2.me/theorems/fadb4923-1e3c-4492-84e1-7d7cb6c82b6b
-- title:
--   P2 M Ground Theory Heights  Heights Inter blocks ne zero restrict c2698d5c05ab: P2 M Ground Theory Heights  Heights Inter blocks ne zero restrict c2698d5c05ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter blocks ne zero restrict c2698d5c05ab construction uses the P2 M Ground Theory Heights  Heights Inter blocks ne zero restrict c2698d5c05ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L21-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogFirstCoordinate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_blocks_ne_zero_restrict_c2698d5c05ab {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {z : (Σ k', ι' k') → ℂ} (hz : ∀ k', ∃ i', z ⟨k', i'⟩ ≠ 0) (k : K) : ∃ i, z (v ⟨k, i⟩) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«blocks_ne_zero_restrict» := P2M_GroundTheory_Heights__Heights_Inter_blocks_ne_zero_restrict_c2698d5c05ab
