-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_SupNormEquality_equiv_4ada4e93fda3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_SupNormEquality_equiv_4ada4e93fda3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:17:05.731328+00:00
-- url     : https://prove2.me/theorems/1ca2d334-0410-4238-965f-49e20e0090f5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Sup Norm Equality equiv 4ada4e93fda3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Sup Norm Equalit
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Sup Norm Equality equiv 4ada4e93fda3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Sup Norm Equality equiv 4ada4e93fda3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L267-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L267-L289

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_SupNormEquality_equiv_4ada4e93fda3 : Heights.SupNormEquality.Statement ↔ IndefiniteRowSideFullHecke.Close.SupNormEquality.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«SupNormEquality».«equiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_SupNormEquality_equiv_4ada4e93fda3
