-- Prove2me | Theorems.Thm_PermanentRollout_finiteFree_maximalFiber_finrank
-- name    : PermanentRollout.finiteFree_maximalFiber_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/2a90b4d5-41a2-43d5-bca9-9775a8faf0ad
-- title:
--   PermanentRollout.finiteFree_maximalFiber_finrank
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout

theorem PermanentRollout.finiteFree_maximalFiber_finrank
    {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Module.Free R S]
    (p : Ideal R) [p.IsMaximal] :
    Module.finrank (R ⧸ p)
      (S ⧸ p.map (algebraMap R S)) = Module.finrank R S := by sorry
