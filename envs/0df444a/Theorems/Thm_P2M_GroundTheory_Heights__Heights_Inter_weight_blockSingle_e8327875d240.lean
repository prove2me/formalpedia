-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_weight_blockSingle_e8327875d240
-- name    : P2M_GroundTheory_Heights__Heights_Inter_weight_blockSingle_e8327875d240
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:48.956879+00:00
-- url     : https://prove2.me/theorems/78bc4d53-cd95-403b-8b88-d6b64a47a27a
-- title:
--   P2 M Ground Theory Heights  Heights Inter weight block Single e8327875d240: P2 M Ground Theory Heights  Heights Inter weight block Single e8327875d240
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter weight block Single e8327875d240 construction uses the P2 M Ground Theory Heights  Heights Inter weight block Single e8327875d240 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreSum.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreSum.lean#L17-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
variable {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_weight_blockSingle_e8327875d240 (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) d = fun k => ∑ i, d ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«weight_blockSingle» := P2M_GroundTheory_Heights__Heights_Inter_weight_blockSingle_e8327875d240
