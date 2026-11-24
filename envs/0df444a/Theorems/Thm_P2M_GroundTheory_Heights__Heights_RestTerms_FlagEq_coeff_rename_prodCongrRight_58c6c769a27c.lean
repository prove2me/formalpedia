-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rename_prodCongrRight_58c6c769a27c
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rename_prodCongrRight_58c6c769a27c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:31:26.136332+00:00
-- url     : https://prove2.me/theorems/7d2b2708-fc6a-4674-9103-cf6f1841b48f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff rename prod Congr Right 58c6c769a27c: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff rename prod Congr Right 58c6c769a27c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff rename prod Congr Right 58c6c769a27c construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff rename prod Congr Right 58c6c769a27c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L49-L58

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rename_prodCongrRight_58c6c769a27c {R : Type*} [CommSemiring R] (w : Fin f → Equiv.Perm (Fin N))
    (P : MvPolynomial (Fin f × Fin N) R) (d : Fin f × Fin N →₀ ℕ) :
    coeff d (rename (Equiv.prodCongrRight w) P) =
      coeff (Finsupp.equivFunOnFinite.symm fun v => d (Equiv.prodCongrRight w v)) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«coeff_rename_prodCongrRight» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rename_prodCongrRight_58c6c769a27c
