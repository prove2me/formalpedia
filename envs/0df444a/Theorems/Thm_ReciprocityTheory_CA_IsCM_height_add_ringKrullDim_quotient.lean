-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCM_height_add_ringKrullDim_quotient
-- name    : ReciprocityTheory.CA.IsCM.height_add_ringKrullDim_quotient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:34.002913+00:00
-- url     : https://prove2.me/theorems/cddcc117-0b5a-4c8a-b3e5-d264746379fb
-- title:
--   Is CM: height add ring Krull Dim quotient
-- statement:
--   The Is CM construction uses the height add ring Krull Dim quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean#L72-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean#L72-L101

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularOfLeHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem ReciprocityTheory.CA.IsCM.height_add_ringKrullDim_quotient (h : IsCM R) (P : Ideal R) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) = ringKrullDim R := by sorry
