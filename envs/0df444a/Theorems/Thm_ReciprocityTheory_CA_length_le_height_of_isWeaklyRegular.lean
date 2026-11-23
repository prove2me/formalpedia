-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_length_le_height_of_isWeaklyRegular
-- name    : ReciprocityTheory.CA.length_le_height_of_isWeaklyRegular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:49.538949+00:00
-- url     : https://prove2.me/theorems/8bd2ac5b-a9cf-4dc6-81e9-3b17bb9f0456
-- title:
--   CA: length le height of is Weakly Regular
-- statement:
--   The CA construction uses the length le height of is Weakly Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean#L24-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/LocDim.lean#L24-L45

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

theorem ReciprocityTheory.CA.length_le_height_of_isWeaklyRegular {R : Type*} [CommRing R] [IsNoetherianRing R]
    (Q : Ideal R) [Q.IsPrime] {rs : List R} (hrs : ∀ x ∈ rs, x ∈ Q) (reg : IsWeaklyRegular R rs) :
    (rs.length : ℕ∞) ≤ Q.height := by sorry
