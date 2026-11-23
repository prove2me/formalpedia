-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_isCM_iff_isCMMod
-- name    : ReciprocityTheory.CA.isCM_iff_isCMMod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:31.875797+00:00
-- url     : https://prove2.me/theorems/71810c90-1ba8-4c3c-91ba-bbe5b8e69ed7
-- title:
--   CA: is CM iff is CMMod
-- statement:
--   The CA construction uses the is CM iff is CMMod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L9-L15

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

theorem ReciprocityTheory.CA.isCM_iff_isCMMod : IsCM R ↔ IsCMMod R R := by sorry
