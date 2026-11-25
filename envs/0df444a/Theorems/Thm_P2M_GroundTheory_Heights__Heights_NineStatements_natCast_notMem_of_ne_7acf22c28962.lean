-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_natCast_notMem_of_ne_7acf22c28962
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_natCast_notMem_of_ne_7acf22c28962
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:32.299139+00:00
-- url     : https://prove2.me/theorems/4f83b923-6b04-4721-a3da-dbc8d6c212a6
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements nat Cast not Mem of ne 7acf22c28962: P2 M Ground Theory Heights  Heights Nine Statements nat Cast not Mem of ne 7acf22c28962
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements nat Cast not Mem of ne 7acf22c28962 construction uses the P2 M Ground Theory Heights  Heights Nine Statements nat Cast not Mem of ne 7acf22c28962 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigenInputs.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigenInputs.lean#L43-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem P2M_GroundTheory_Heights__Heights_NineStatements_natCast_notMem_of_ne_7acf22c28962 {L : Type} [Field L] [NumberField L] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (𝔓 : HeightOneSpectrum (𝓞 L)) (h : (p : 𝓞 L) ∈ 𝔓.asIdeal) : (q : 𝓞 L) ∉ 𝔓.asIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«natCast_notMem_of_ne» := P2M_GroundTheory_Heights__Heights_NineStatements_natCast_notMem_of_ne_7acf22c28962
