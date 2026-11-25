-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_core_44f39e587f33
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_core_44f39e587f33
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:21.191948+00:00
-- url     : https://prove2.me/theorems/4f820d24-8c2b-5bc6-a7e9-0a2df9bb766f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq core 44f39e587f33: P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq core 44f39e587f33
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq core 44f39e587f33 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq core 44f39e587f33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/RestAt.lean#L15-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/RestAt.lean#L15-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_DegPolynomialIsHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealTransferOfSyzygy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StaircaseIsHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_RestAt
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_core_44f39e587f33 (hA : RestBound.Statement)
    (f r a j k : ℕ) (c : SmallBlock) (bot : Bool) (h : r + a = j + k)
    (hf : 1 ≤ f) (hr : 1 ≤ r) (ha : 1 ≤ a) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hsp : ∀ m τ, rootRingToReal f (r + a) j k h (smallPowerSum f r a c m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f j k bot m τ)
    (hF : rootRingToReal f (r + a) j k h (restPolynomial f r a c) = IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot)
    (hD : rootRingToReal f (r + a) j k h (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot)
    (hn : f * (r * a) = IndefiniteRowSideFullHecke.RestTerms.nDim f j k)
    (I : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ) (hI : IndefiniteRowSideFullHecke.RestTerms.IsFlagIntegral f j k I)
    (vol : ℝ) (hvol : 0 < vol) (P : Set ℕ) (B₀ : ℝ)
    (hB₀ : 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀)
    (σ : ℕ → ℕ → Fin f → Fin f × Bool) (Q : Fin f → ℕ → IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hQ : IndefiniteRowSideFullHecke.RestTerms.IsPsumDecomp f j k (IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot) Q) :
    Summable (fun p : IndefiniteRowSideFullHecke.RestTerms.primesOver P B₀ =>
        IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p.1) ∧
      |∑' p : IndefiniteRowSideFullHecke.RestTerms.primesOver P B₀, IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p.1| ≤
        1.6 * ((IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1) * vol *
          |I (IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot)| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestBoundEq».«core» := P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_core_44f39e587f33
