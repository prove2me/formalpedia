-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rho_antisym_e85d46ff9ddc
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rho_antisym_e85d46ff9ddc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:38.98693+00:00
-- url     : https://prove2.me/theorems/accfdf38-98d4-4e4b-a56d-2cdfd83cf22a
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff rho antisym e85d46ff9ddc: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff rho antisym e85d46ff9ddc
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff rho antisym e85d46ff9ddc construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff rho antisym e85d46ff9ddc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L60-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
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
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq
variable {f N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rho_antisym_e85d46ff9ddc {R : Type*} [CommRing R] (P : MvPolynomial (Fin f × Fin N) R) :
    coeff (rho f N) (∑ w : Fin f → Equiv.Perm (Fin N),
        ((permSign f N w : ℤ) : R) • rename (Equiv.prodCongrRight w) P) =
      ∑ w, ((permSign f N w : ℤ) : R) * coeff (stairExp f N w) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«coeff_rho_antisym» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rho_antisym_e85d46ff9ddc
