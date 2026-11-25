-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_locDens_perm_952114d1e445
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_locDens_perm_952114d1e445
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:02.267833+00:00
-- url     : https://prove2.me/theorems/c5945070-0d51-55f8-be1b-558723fa1412
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change loc Dens perm 952114d1e445: P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change loc Dens perm 952114d1e445
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change loc Dens perm 952114d1e445 construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change loc Dens perm 952114d1e445 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereCompactChange.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereCompactChange.lean#L17-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereCompactChange
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_locDens_perm_952114d1e445 (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (σ : Equiv.Perm (Fin e))
    (j : Fin A.n) (y : Fin e → ℂ) : locDens A (Φ ∘ σ) j y = locDens A Φ j y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereCompactChange».«locDens_perm» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_locDens_perm_952114d1e445
