-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_HermitianExtension_degree_range_incl_0fb1c2c0025b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_HermitianExtension_degree_range_incl_0fb1c2c0025b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:44:25.65792+00:00
-- url     : https://prove2.me/theorems/71f92888-e6a6-5ad9-b465-0b7ab112358b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels Hermitian Extension degree range incl 0fb1c2c0025b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernel
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels Hermitian Extension degree range incl 0fb1c2c0025b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels Hermitian Extension degree range incl 0fb1c2c0025b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/DegreeRangeIncl.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/DegreeRangeIncl.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DegreeTopEqArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DegreeRangeIncl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField TensorProduct GroundTheory.Heights₂.Heights
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_HermitianExtension_degree_range_incl_0fb1c2c0025b {K : Type} [Field K] [NumberField K]
    {E' E E'' : HermitianBundle.{0} K} (Y : HermitianExtension E' E E'') :
    E.degree (LinearMap.range Y.incl) = E'.arithDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«HermitianExtension».«degree_range_incl» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_HermitianExtension_degree_range_incl_0fb1c2c0025b
