-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrict_gmfOut_7b9edc99d122
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrict_gmfOut_7b9edc99d122
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:21.461843+00:00
-- url     : https://prove2.me/theorems/7c248dec-4e74-475a-9e90-6641a57ecef9
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top restrict gmf Out 7b9edc99d122: P2 M Ground Theory Heights  Heights Rest Terms Top restrict gmf Out 7b9edc99d122
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top restrict gmf Out 7b9edc99d122 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top restrict gmf Out 7b9edc99d122 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L92-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L92-L124

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrict_gmfOut_7b9edc99d122 (f r a : ℕ) (c : SmallBlock) (κ : ℚ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f)
    (hq : ∀ σ, σ ≠ τ → q σ ≤ r * a)
    (he : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') ≤ e) :
    restrictToBlock f (r + a) τ (gmfOut f r a c κ q e) =
      ((Nat.multinomial Finset.univ (mstar f r a q e τ) : ℚ) *
          ∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ)) •
        toN (r + a) (blockOut r a c κ (q τ) (mstar f r a q e τ τ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«restrict_gmfOut» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrict_gmfOut_7b9edc99d122
