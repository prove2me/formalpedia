-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegralReal_transfer_of_syzygy_46d401452df6
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegralReal_transfer_of_syzygy_46d401452df6
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:27.900726+00:00
-- url     : https://prove2.me/theorems/2f9ead2a-ca3f-5c66-827d-2e94e75ee5a8
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq flag Integral Real transfer of syzygy 46d401452df6: P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq flag Integral Real transfe
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq flag Integral Real transfer of syzygy 46d401452df6 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq flag Integral Real transfer of syzygy 46d401452df6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealTransferOfSyzygy.lean#L182-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealTransferOfSyzygy.lean#L182-L219

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealTransferOfSyzygy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegralReal_transfer_of_syzygy_46d401452df6 (f N j k : ℕ) (h : N = j + k) (F : RootRing f N)
    (Q₀ : ℕ → Fin f → RootRing f N) (hQ₀ : IsPowerSumDecomposition f N F Q₀)
    (Q' : Fin f → ℕ → IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hQ' : rootRingToReal f N j k h F =
      ∑ τ : Fin f, ∑ m ∈ Icc 1 (j + k), IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * Q' τ m)
    (m : ℕ) (τ : Fin f) (G : RootRing f N)
    (hS : ∀ S : ℕ → Fin f → RootRing f N, IsPowerSumDecomposition f N 0 S →
      flagIntegral f N (G * S m τ) = 0) :
    flagIntegralReal f (j + k) (rootRingToReal f N j k h G * Q' τ m) =
      (flagIntegral f N (G * Q₀ m τ) : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestBoundEq».«flagIntegralReal_transfer_of_syzygy» := P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegralReal_transfer_of_syzygy_46d401452df6
