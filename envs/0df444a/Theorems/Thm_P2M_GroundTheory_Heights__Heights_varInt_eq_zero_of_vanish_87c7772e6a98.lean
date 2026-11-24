-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_varInt_eq_zero_of_vanish_87c7772e6a98
-- name    : P2M_GroundTheory_Heights__Heights_varInt_eq_zero_of_vanish_87c7772e6a98
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:30.496405+00:00
-- url     : https://prove2.me/theorems/f95299fd-bb66-4307-a8c5-0dc6022d1516
-- title:
--   P2 M Ground Theory Heights  Heights var Int eq zero of vanish 87c7772e6a98: P2 M Ground Theory Heights  Heights var Int eq zero of vanish 87c7772e6a98
-- statement:
--   The P2 M Ground Theory Heights  Heights var Int eq zero of vanish 87c7772e6a98 construction uses the P2 M Ground Theory Heights  Heights var Int eq zero of vanish 87c7772e6a98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimit.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimit.lean#L14-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOffZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOnZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalLimitGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimit
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_varInt_eq_zero_of_vanish_87c7772e6a98 {n k : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) (hf : ∀ x ∈ zeroSet W, f x = 0) :
    varInt W k f φ = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«varInt_eq_zero_of_vanish» := P2M_GroundTheory_Heights__Heights_varInt_eq_zero_of_vanish_87c7772e6a98
