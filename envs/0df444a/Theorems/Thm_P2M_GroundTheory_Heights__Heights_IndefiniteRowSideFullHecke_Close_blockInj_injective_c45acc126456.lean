-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_blockInj_injective_c45acc126456
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_blockInj_injective_c45acc126456
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:18.100806+00:00
-- url     : https://prove2.me/theorems/465c28f7-e1a3-45a4-8875-58279c63ab28
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close block Inj injective c45acc126456: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close block Inj injective
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close block Inj injective c45acc126456 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close block Inj injective c45acc126456 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L40-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_blockInj_injective_c45acc126456 (k₀ : ι) :
    Function.Injective (fun i : Fin (n k₀ + 1) ↦ (⟨k₀, i⟩ : Coord n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«blockInj_injective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_blockInj_injective_c45acc126456
