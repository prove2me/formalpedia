-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_psumExpansion_cac4269a2de6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_psumExpansion_cac4269a2de6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:07.489257+00:00
-- url     : https://prove2.me/theorems/71711d62-caa0-5a15-bbde-0924e6cf2198
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR class Num psum Expansion cac4269a2de6: P2 M Ground Theory Heights  Heights Numbers DVR class Num psum Expansion cac4269a2de6
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR class Num psum Expansion cac4269a2de6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR class Num psum Expansion cac4269a2de6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L553-L566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L553-L566

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
  {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_psumExpansion_cac4269a2de6 (u v : Fin N → K → ℤ) (k : ℕ) (i : Fin N) {Q : List (K → ℤ)}
    {d : ℕ} (hQ : Q.length + k = d + 1) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim u v) (psumExpansion N k i) Q W = geoVal (listNum W Q d) k (u i) (v i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«classNum_psumExpansion» := P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_psumExpansion_cac4269a2de6
