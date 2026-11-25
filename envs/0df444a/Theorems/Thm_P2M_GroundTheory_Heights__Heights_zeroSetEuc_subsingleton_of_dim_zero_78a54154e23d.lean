-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_zeroSetEuc_subsingleton_of_dim_zero_78a54154e23d
-- name    : P2M_GroundTheory_Heights__Heights_zeroSetEuc_subsingleton_of_dim_zero_78a54154e23d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:38.174802+00:00
-- url     : https://prove2.me/theorems/bc0e0904-82bd-48b6-a668-ff8375dd6eb0
-- title:
--   P2 M Ground Theory Heights  Heights zero Set Euc subsingleton of dim zero 78a54154e23d: P2 M Ground Theory Heights  Heights zero Set Euc subsingleton of dim zero 78a54154e23d
-- statement:
--   The P2 M Ground Theory Heights  Heights zero Set Euc subsingleton of dim zero 78a54154e23d construction uses the P2 M Ground Theory Heights  Heights zero Set Euc subsingleton of dim zero 78a54154e23d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyLelongMono.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyLelongMono.lean#L15-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarWirtinger
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyLelongMono
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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_zeroSetEuc_subsingleton_of_dim_zero_78a54154e23d {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((0 : ℕ) : WithBot ℕ∞))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ zeroSetEuc J) :
    ∀ y ∈ zeroSetEuc J, y = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«zeroSetEuc_subsingleton_of_dim_zero» := P2M_GroundTheory_Heights__Heights_zeroSetEuc_subsingleton_of_dim_zero_78a54154e23d
