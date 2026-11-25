-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DenseSec_factor__comp_factor__7e1aebb4d17b
-- name    : P2M_GlobalTheory_DenseSec_factor__comp_factor__7e1aebb4d17b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:44.629479+00:00
-- url     : https://prove2.me/theorems/3ea09749-2a3f-4b32-9378-340f2a771276
-- title:
--   P2 M Global Theory Dense Sec factor  comp factor  7e1aebb4d17b: P2 M Global Theory Dense Sec factor  comp factor  7e1aebb4d17b
-- statement:
--   The P2 M Global Theory Dense Sec factor  comp factor  7e1aebb4d17b construction uses the P2 M Global Theory Dense Sec factor  comp factor  7e1aebb4d17b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSectionLiftingResidueValues.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSectionLiftingResidueValues.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSectionLiftingResidueValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.DenseSec

theorem P2M_GlobalTheory_DenseSec_factor__comp_factor__7e1aebb4d17b {P R : Type} [CommRing P] [CommRing R] [Algebra P R] {I J K : Ideal R}
    (hIJ : I ≤ J) (hJK : J ≤ K) :
    (Ideal.Quotient.factorₐ P hJK).comp (Ideal.Quotient.factorₐ P hIJ) =
      Ideal.Quotient.factorₐ P (hIJ.trans hJK) := by sorry

alias «GlobalTheory».«DenseSec».«factorₐ_comp_factorₐ» := P2M_GlobalTheory_DenseSec_factor__comp_factor__7e1aebb4d17b
