-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_of_isHomogeneous_lex_28d8cf3999da
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_of_isHomogeneous_lex_28d8cf3999da
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:16.730649+00:00
-- url     : https://prove2.me/theorems/59efbfa7-4c89-49c7-9282-95d613629269
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal of is Homogeneous lex 28d8cf3999da: P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal of is Homogeneous lex 28d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal of is Homogeneous lex 28d8cf3999da construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal of is Homogeneous lex 28d8cf3999da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L63-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L63-L71

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_of_isHomogeneous_lex_28d8cf3999da (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)}
    (hI : letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
      I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))) :
    IsMultiHomogIdeal I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isMultiHomogIdeal_of_isHomogeneous_lex» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_of_isHomogeneous_lex_28d8cf3999da
