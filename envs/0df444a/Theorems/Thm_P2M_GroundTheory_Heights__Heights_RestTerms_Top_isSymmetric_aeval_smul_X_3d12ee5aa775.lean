-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isSymmetric_aeval_smul_X_3d12ee5aa775
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_isSymmetric_aeval_smul_X_3d12ee5aa775
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:59.561522+00:00
-- url     : https://prove2.me/theorems/ef713e93-f186-4cff-8763-1d72c3c5499c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top is Symmetric aeval smul X 3d12ee5aa775: P2 M Ground Theory Heights  Heights Rest Terms Top is Symmetric aeval smul X 3d12ee5aa775
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top is Symmetric aeval smul X 3d12ee5aa775 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top is Symmetric aeval smul X 3d12ee5aa775 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/POtherFactorFormula.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/POtherFactorFormula.lean#L17-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_POtherFactorFormula
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_isSymmetric_aeval_smul_X_3d12ee5aa775 {N : ℕ} (s : ℚ) {p : MvPolynomial (Fin N) ℚ} (hp : p.IsSymmetric) :
    (aeval (fun i : Fin N => C s * X i) p).IsSymmetric := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«isSymmetric_aeval_smul_X» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_isSymmetric_aeval_smul_X_3d12ee5aa775
