-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarIntAdd_ringKrullDim_eq_of_injective_finite_2e89a82355c9
-- name    : P2M_GroundTheory_Heights__Heights_VarIntAdd_ringKrullDim_eq_of_injective_finite_2e89a82355c9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:42:03.368812+00:00
-- url     : https://prove2.me/theorems/59dca24d-9506-4932-a5f6-c8ee0abe1f3d
-- title:
--   P2 M Ground Theory Heights  Heights Var Int Add ring Krull Dim eq of injective finite 2e89a82355c9: P2 M Ground Theory Heights  Heights Var Int Add ring Krull Dim eq of injective finite 2e89a82355c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Int Add ring Krull Dim eq of injective finite 2e89a82355c9 construction uses the P2 M Ground Theory Heights  Heights Var Int Add ring Krull Dim eq of injective finite 2e89a82355c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntAdd.lean#L16-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntAdd.lean#L16-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.VarIntAdd

theorem P2M_GroundTheory_Heights__Heights_VarIntAdd_ringKrullDim_eq_of_injective_finite_2e89a82355c9 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hfin : f.Finite) : ringKrullDim S = ringKrullDim R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarIntAdd».«ringKrullDim_eq_of_injective_finite» := P2M_GroundTheory_Heights__Heights_VarIntAdd_ringKrullDim_eq_of_injective_finite_2e89a82355c9
