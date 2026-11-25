-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_mem_heightOneSpectrum_c3aeab300187
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_mem_heightOneSpectrum_c3aeab300187
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:04:39.396532+00:00
-- url     : https://prove2.me/theorems/95588d57-d854-42af-9160-66d727270ac5
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements exists prime mem height One Spectrum c3aeab300187: P2 M Ground Theory Heights  Heights Nine Statements exists prime mem height One Spectrum c3aeab30
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements exists prime mem height One Spectrum c3aeab300187 construction uses the P2 M Ground Theory Heights  Heights Nine Statements exists prime mem height One Spectrum c3aeab300187 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PNormCountBound.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PNormCountBound.lean#L27-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PNormCountBound
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

theorem P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_mem_heightOneSpectrum_c3aeab300187 {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ v.asIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«exists_prime_mem_heightOneSpectrum» := P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_mem_heightOneSpectrum_c3aeab300187
