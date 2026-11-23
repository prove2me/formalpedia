-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
-- name    : ReciprocityTheory.CA.DepthGE.of_ringEquiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:25.462093+00:00
-- url     : https://prove2.me/theorems/41a4e643-62c1-470d-b7a2-840e41dcc23c
-- title:
--   Depth GE: of ring Equiv
-- statement:
--   The Depth GE construction uses the of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L131-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L131-L144

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

theorem ReciprocityTheory.CA.DepthGE.of_ringEquiv {S : Type*} [CommRing S] [IsLocalRing S] (e : R ≃+* S) {n : ℕ}
    (h : DepthGE R n) : DepthGE S n := by sorry
