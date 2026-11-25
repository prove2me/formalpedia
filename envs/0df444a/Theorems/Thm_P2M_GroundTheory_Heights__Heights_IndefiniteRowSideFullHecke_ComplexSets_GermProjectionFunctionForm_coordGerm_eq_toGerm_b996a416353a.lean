-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_coordGerm_eq_toGerm_b996a416353a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_coordGerm_eq_toGerm_b996a416353a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:48.323604+00:00
-- url     : https://prove2.me/theorems/05032740-fcb5-4c31-b523-5d4d40f974f8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Projection Function Form coord Germ eq to Germ b996a416353a: P2 M Ground Theory Heights  Heights Indefinite Row Sid
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Projection Function Form coord Germ eq to Germ b996a416353a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Projection Function Form coord Germ eq to Germ b996a416353a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermProjectionFunctionForm.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermProjectionFunctionForm.lean#L20-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermProjectionFunctionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermProjectionFunctionForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter PrimeGermPrimitivePresentation
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermProjectionFunctionForm
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_coordGerm_eq_toGerm_b996a416353a (w : σ → ℂ) (i : σ) :
    coordGerm w i = toGerm w (mkA (fun z : σ → ℂ => z i)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«GermProjectionFunctionForm».«coordGerm_eq_toGerm» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_coordGerm_eq_toGerm_b996a416353a
