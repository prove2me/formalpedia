-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_add_970f926c8cdd
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_add_970f926c8cdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:52.697165+00:00
-- url     : https://prove2.me/theorems/16eacb2d-7035-40f7-bf8b-013d3a0e06cb
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral add 970f926c8cdd: P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral add 970f926c8cdd
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral add 970f926c8cdd construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral add 970f926c8cdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L221-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L221-L223

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
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
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
variable (f r a : ℕ) (c : SmallBlock)

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_add_970f926c8cdd (f N : ℕ) (Φ Ψ : RootRing f N) :
    flagIntegral f N (Φ + Ψ) = flagIntegral f N Φ + flagIntegral f N Ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«flagIntegral_add» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_add_970f926c8cdd
