-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_isCMMod_congr
-- name    : ReciprocityTheory.CA.isCMMod_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:09.622976+00:00
-- url     : https://prove2.me/theorems/b8e7ab7a-15a7-4c04-923e-255939a3e187
-- title:
--   CA: is CMMod congr
-- statement:
--   The CA construction uses the is CMMod congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L25-L37

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

theorem ReciprocityTheory.CA.isCMMod_congr {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : IsCMMod R M ↔ IsCMMod R N := by sorry
