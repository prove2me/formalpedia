-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_index_span_smul_210a9f4dbdea
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_index_span_smul_210a9f4dbdea
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:32.025737+00:00
-- url     : https://prove2.me/theorems/d676f14e-da3b-5279-8171-2c03a744a83d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle index span smul 210a9f4dbdea: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle index span smul 210a9f4dbdea construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle index span smul 210a9f4dbdea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineDegreeBundle.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineDegreeBundle.lean#L13-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LineDegreeBundleStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLineDegreeBundle
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
open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder nonZeroDivisors
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_index_span_smul_210a9f4dbdea {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [IsDomain R] [Module.IsTorsionFree R N] {x : N} (hx : x ≠ 0) (a : R) :
    (Submodule.span R {a • x}).toAddSubgroup.index =
      Submodule.cardQuot (Ideal.span {a} : Ideal R) * (Submodule.span R {x}).toAddSubgroup.index := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«LineDegreeBundle».«index_span_smul» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_index_span_smul_210a9f4dbdea
