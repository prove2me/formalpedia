-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_mstar_mem_91aff65fe145
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_mstar_mem_91aff65fe145
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:23.229466+00:00
-- url     : https://prove2.me/theorems/1b754f03-7fe2-43f3-badd-90da224f9da0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top mstar mem 91aff65fe145: P2 M Ground Theory Heights  Heights Rest Terms Top mstar mem 91aff65fe145
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top mstar mem 91aff65fe145 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top mstar mem 91aff65fe145 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L64-L75

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_mstar_mem_91aff65fe145 (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f)
    (he : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') ≤ e) :
    mstar f r a q e τ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«mstar_mem» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_mstar_mem_91aff65fe145
