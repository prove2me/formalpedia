-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_norm_unit_16f7003adcaf
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_norm_unit_16f7003adcaf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:44.653843+00:00
-- url     : https://prove2.me/theorems/6c25ccac-f88b-49c4-a9d2-6dca4f910716
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index norm unit 16f7003adcaf: P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index norm unit 16f7003adcaf
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index norm unit 16f7003adcaf construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index norm unit 16f7003adcaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalLatticeIndex.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalLatticeIndex.lean#L16-L24

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalLatticeIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_norm_unit_16f7003adcaf (u : (v.adicCompletionIntegers K)ˣ) :
    ‖((u : v.adicCompletionIntegers K) : v.adicCompletion K)‖ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«LocalLatticeIndex».«norm_unit» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_norm_unit_16f7003adcaf
