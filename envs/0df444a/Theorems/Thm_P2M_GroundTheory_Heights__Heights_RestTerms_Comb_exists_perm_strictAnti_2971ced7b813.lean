-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_exists_perm_strictAnti_2971ced7b813
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_exists_perm_strictAnti_2971ced7b813
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:19:53.310946+00:00
-- url     : https://prove2.me/theorems/f537c654-296c-438c-ad14-0d2f41791928
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb exists perm strict Anti 2971ced7b813: P2 M Ground Theory Heights  Heights Rest Terms Comb exists perm strict Anti 2971ced7b813
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb exists perm strict Anti 2971ced7b813 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb exists perm strict Anti 2971ced7b813 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L210-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L210-L216

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_exists_perm_strictAnti_2971ced7b813 {u : Fin m → ℕ} (hu : Function.Injective u) :
    ∃ σ : Perm (Fin m), StrictAnti (u ∘ σ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«exists_perm_strictAnti» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_exists_perm_strictAnti_2971ced7b813
