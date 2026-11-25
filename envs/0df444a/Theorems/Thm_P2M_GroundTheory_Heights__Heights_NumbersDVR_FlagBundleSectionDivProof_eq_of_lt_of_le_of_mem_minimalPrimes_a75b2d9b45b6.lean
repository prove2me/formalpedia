-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_eq_of_lt_of_le_of_mem_minimalPrimes_a75b2d9b45b6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_eq_of_lt_of_le_of_mem_minimalPrimes_a75b2d9b45b6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:42.199391+00:00
-- url     : https://prove2.me/theorems/e712b729-b3e3-4ace-a417-070e70c1103e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div Proof eq of lt of le of mem minimal Primes a75b2d9b45b6: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div Proof eq of lt of le of mem minimal Primes a75b2d9b45b6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div Proof eq of lt of le of mem minimal Primes a75b2d9b45b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionDiv.lean#L18-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionDiv.lean#L18-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMultAtOfSaturated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionDiv
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionDivProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_eq_of_lt_of_le_of_mem_minimalPrimes_a75b2d9b45b6 {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [P.IsPrime] [Q.IsPrime] {x : A}
    (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P < Q) (hQW : Q ≤ W) : Q = W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleSectionDivProof».«eq_of_lt_of_le_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_eq_of_lt_of_le_of_mem_minimalPrimes_a75b2d9b45b6
