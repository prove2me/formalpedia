-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_eval_top_e1c72c19af4e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_eval_top_e1c72c19af4e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:48.737589+00:00
-- url     : https://prove2.me/theorems/45ff5dbb-b9d4-4d54-a849-9d581838f7ce
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Proportional eval top e1c72c19af4e: P2 M Ground Theory Heights  Heights Rest Terms Flag Proportional eval top e1c72c19af4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Proportional eval top e1c72c19af4e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Proportional eval top e1c72c19af4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StaircaseIsHomogeneous.lean#L39-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StaircaseIsHomogeneous.lean#L39-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvAtTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvPolynomialReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvMonomialReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStepReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealRepresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StaircaseIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagProportional

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_eval_top_e1c72c19af4e (f j k : ℕ) (L : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ)
    (hL : ∀ (m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k), 1 ≤ m →
      m ≤ IndefiniteRowSideFullHecke.RestTerms.dimFl f j k → G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k - m) →
        L (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0)
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (hG : G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k)) (c : ℝ)
    (hc : G - C c * monomial (Coinv.staircase f (j + k)) 1 ∈ Coinv.psumIdeal ℝ f (j + k)) :
    L G = c * L (monomial (Coinv.staircase f (j + k)) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagProportional».«eval_top» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_eval_top_e1c72c19af4e
