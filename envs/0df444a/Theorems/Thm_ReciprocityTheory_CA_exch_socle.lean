-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_exch_socle
-- name    : ReciprocityTheory.CA.exch_socle
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:45.422299+00:00
-- url     : https://prove2.me/theorems/e571810b-41ce-4771-87ee-da328f900788
-- title:
--   CA: exch socle
-- statement:
--   The CA construction uses the exch socle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L30-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L30-L48

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem ReciprocityTheory.CA.exch_socle {x y : R} (hy : y ∈ maximalIdeal R) (rx : IsSMulRegular M x)
    (ry : IsSMulRegular M y) {a : M} (ha : a ∉ x • (⊤ : Submodule R M))
    (hma : ∀ z ∈ maximalIdeal R, z • a ∈ x • (⊤ : Submodule R M)) :
    ∃ b : M, b ∉ y • (⊤ : Submodule R M) ∧
      ∀ z ∈ maximalIdeal R, z • b ∈ y • (⊤ : Submodule R M) := by sorry
