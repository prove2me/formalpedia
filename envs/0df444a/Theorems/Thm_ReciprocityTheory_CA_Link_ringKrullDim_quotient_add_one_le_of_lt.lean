-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_Link_ringKrullDim_quotient_add_one_le_of_lt
-- name    : ReciprocityTheory.CA.Link.ringKrullDim_quotient_add_one_le_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:16.242018+00:00
-- url     : https://prove2.me/theorems/49e33dee-c166-47bd-96be-02dc34288e6c
-- title:
--   Link: ring Krull Dim quotient add one le of lt
-- statement:
--   The Link construction uses the ring Krull Dim quotient add one le of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/WeakRegularity/RingKrullDimQuotientAddOneLeOfLt.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/WeakRegularity/RingKrullDimQuotientAddOneLeOfLt.lean#L10-L17

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_WeakRegularity_GorIndepStatement
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_WeakRegularity_RingKrullDimQuotientAddOneLeOfLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA ReciprocityTheory.CA.Link
open IsLocalRing
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.CA.Link.ringKrullDim_quotient_add_one_le_of_lt {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : q < p) : ringKrullDim (R ⧸ p) + 1 ≤ ringKrullDim (R ⧸ q) := by sorry
