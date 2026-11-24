-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MassFinite_exists_frame_37c550a38a85
-- name    : P2M_GroundTheory_Heights__Heights_MassFinite_exists_frame_37c550a38a85
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:50.04847+00:00
-- url     : https://prove2.me/theorems/4ca932b2-a6f7-4238-8827-b1b3b4f468a4
-- title:
--   P2 M Ground Theory Heights  Heights Mass Finite exists frame 37c550a38a85: P2 M Ground Theory Heights  Heights Mass Finite exists frame 37c550a38a85
-- statement:
--   The P2 M Ground Theory Heights  Heights Mass Finite exists frame 37c550a38a85 construction uses the P2 M Ground Theory Heights  Heights Mass Finite exists frame 37c550a38a85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFinite.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFinite.lean#L17-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite
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
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.MassFinite

theorem P2M_GroundTheory_Heights__Heights_MassFinite_exists_frame_37c550a38a85 {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MassFinite».«exists_frame» := P2M_GroundTheory_Heights__Heights_MassFinite_exists_frame_37c550a38a85
