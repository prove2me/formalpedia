-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_ringKrullDim_le_of_finite_37324c18be2a
-- name    : P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_ringKrullDim_le_of_finite_37324c18be2a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:39.430302+00:00
-- url     : https://prove2.me/theorems/723b1d8d-86f7-5b53-881b-fed27302bc0b
-- title:
--   P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski ring Krull Dim le of finite 37324c18be2a: P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski ring Krull Dim le of finit
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski ring Krull Dim le of finite 37324c18be2a construction uses the P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski ring Krull Dim le of finite 37324c18be2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLocalDimUpperZariski.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLocalDimUpperZariski.lean#L19-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLocalDimUpperZariski
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
open MvPolynomial Matrix ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_ringKrullDim_le_of_finite_37324c18be2a {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) : ringKrullDim S ≤ ringKrullDim R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceLocalDimUpperZariski».«ringKrullDim_le_of_finite» := P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_ringKrullDim_le_of_finite_37324c18be2a
