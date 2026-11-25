-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_mk_mem_maximalIdeal_quot
-- name    : ReciprocityTheory.CA.mk_mem_maximalIdeal_quot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:40.843717+00:00
-- url     : https://prove2.me/theorems/0c083ccd-b961-427d-9e4d-de8b15c4a6d1
-- title:
--   CA: mk mem maximal Ideal quot
-- statement:
--   The CA construction uses the mk mem maximal Ideal quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L72-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L72-L91

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
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

theorem ReciprocityTheory.CA.mk_mem_maximalIdeal_quot (I : Ideal R) [IsLocalRing (R ⧸ I)] {r : R}
    (hr : r ∈ maximalIdeal R) : Ideal.Quotient.mk I r ∈ maximalIdeal (R ⧸ I) := by sorry
