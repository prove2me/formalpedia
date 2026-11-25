-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_card_quot_span_bba263407b48
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_card_quot_span_bba263407b48
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:06.480059+00:00
-- url     : https://prove2.me/theorems/a3423a16-3fdc-46a2-b6e8-16f3fa364fdb
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index card quot span bba263407b48: P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index card quot span bba263407b48
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index card quot span bba263407b48 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas Local Lattice Index card quot span bba263407b48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalLatticeIndex.lean#L26-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalLatticeIndex.lean#L26-L44

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

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_card_quot_span_bba263407b48 {a : v.adicCompletionIntegers K} (ha : a ≠ 0) :
    (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {a}) : ℝ) =
      ‖(a : v.adicCompletion K)‖⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«LocalLatticeIndex».«card_quot_span» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_card_quot_span_bba263407b48
