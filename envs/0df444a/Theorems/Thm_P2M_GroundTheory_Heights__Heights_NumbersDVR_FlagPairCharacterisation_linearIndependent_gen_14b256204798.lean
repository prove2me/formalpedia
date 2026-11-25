-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_linearIndependent_gen_14b256204798
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_linearIndependent_gen_14b256204798
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:06:27.62655+00:00
-- url     : https://prove2.me/theorems/e0c527e6-eea0-417a-89f4-4e0d14ffa53d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation linear Independent gen 14b256204798: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation linear Indepe
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation linear Independent gen 14b256204798 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation linear Independent gen 14b256204798 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L97-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L97-L133

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairIff
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
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type*}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_linearIndependent_gen_14b256204798 {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    (dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)) {m : Fin N → K → ℤ} {gen : Fin N → E}
    (hmem : ∀ i, gen i ∈ Vs i.succ) (hfr : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B Vs m gen)
    {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) : LinearIndependent Ω gen := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairCharacterisation».«linearIndependent_gen» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_linearIndependent_gen_14b256204798
