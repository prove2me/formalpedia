-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_cross_mem_dae8c470757e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_cross_mem_dae8c470757e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:11.546609+00:00
-- url     : https://prove2.me/theorems/e3de8639-1056-48ca-a24e-03ec5e74829a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor cross mem dae8c470757e: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor cross mem dae8c470757e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor cross mem dae8c470757e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor cross mem dae8c470757e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L63-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L63-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
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
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_cross_mem_dae8c470757e {z : (Σ k, ι k) → Φ} {f g f' g' : MRing ι O} {bf bg bf' bg' : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hf' : IsMultiHomog f' bf')
    (hg' : IsMultiHomog g' bg') (hdeg : ∀ k, (bf k : ℤ) - bg k = bf' k - bg' k)
    (hv : aeval z f = aeval z g) (hv' : aeval z f' = aeval z g') :
    f * g' - f' * g ∈ pointIdeal O z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDivisor».«cross_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_cross_mem_dae8c470757e
