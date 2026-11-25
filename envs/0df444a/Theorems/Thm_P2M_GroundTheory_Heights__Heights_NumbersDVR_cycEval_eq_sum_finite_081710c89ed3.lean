-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_sum_finite_081710c89ed3
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_sum_finite_081710c89ed3
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:15.446544+00:00
-- url     : https://prove2.me/theorems/f8c92c9f-d59c-471e-9fbb-edf32e749f74
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq sum finite 081710c89ed3: P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq sum finite 081710c89ed3
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq sum finite 081710c89ed3 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq sum finite 081710c89ed3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L236-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L236-L241

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_sum_finite_081710c89ed3 {n Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite) :
    cycEval n Z = ∑ W ∈ hZ.toFinset, Z W * n W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cycEval_eq_sum_finite» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_sum_finite_081710c89ed3
