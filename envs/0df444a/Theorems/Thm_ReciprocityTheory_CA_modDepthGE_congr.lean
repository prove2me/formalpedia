-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_modDepthGE_congr
-- name    : ReciprocityTheory.CA.modDepthGE_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:46.884993+00:00
-- url     : https://prove2.me/theorems/0bb1050e-5cb5-4120-ab23-390d21640fd1
-- title:
--   CA: mod Depth GE congr
-- statement:
--   The CA construction uses the mod Depth GE congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L17-L23

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

theorem ReciprocityTheory.CA.modDepthGE_congr {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (n : ℕ) : ModDepthGE R M n ↔ ModDepthGE R N n := by sorry
