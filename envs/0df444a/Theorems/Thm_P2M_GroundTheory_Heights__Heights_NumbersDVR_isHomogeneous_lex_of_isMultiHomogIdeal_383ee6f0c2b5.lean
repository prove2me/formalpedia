-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_lex_of_isMultiHomogIdeal_383ee6f0c2b5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_lex_of_isMultiHomogIdeal_383ee6f0c2b5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:50.150139+00:00
-- url     : https://prove2.me/theorems/fbafb642-55d5-46db-bd05-45246bf26f69
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous lex of is Multi Homog Ideal 383ee6f0c2b5: P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous lex of is Multi Homog Ideal 383e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous lex of is Multi Homog Ideal 383ee6f0c2b5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous lex of is Multi Homog Ideal 383ee6f0c2b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L50-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L50-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
variable [DecidableEq K] [DecidableEq (Lex (Fin (Fintype.card K) → ℕ))]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_lex_of_isMultiHomogIdeal_383ee6f0c2b5 (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
    I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isHomogeneous_lex_of_isMultiHomogIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_lex_of_isMultiHomogIdeal_383ee6f0c2b5
