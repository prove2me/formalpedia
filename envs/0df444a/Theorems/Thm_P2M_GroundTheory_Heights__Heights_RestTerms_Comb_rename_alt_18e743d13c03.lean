-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_rename_alt_18e743d13c03
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_rename_alt_18e743d13c03
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:30.543861+00:00
-- url     : https://prove2.me/theorems/0b080ce9-d92d-41c4-84ac-a9b009f2ac43
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb rename alt 18e743d13c03: P2 M Ground Theory Heights  Heights Rest Terms Comb rename alt 18e743d13c03
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb rename alt 18e743d13c03 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb rename alt 18e743d13c03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L38-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_rename_alt_18e743d13c03 (v : Fin m → ℕ) (σ : Perm (Fin m)) :
    rename σ (alt v) = (Perm.sign σ : ℤ) • alt v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«rename_alt» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_rename_alt_18e743d13c03
