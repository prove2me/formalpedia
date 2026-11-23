-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
-- name    : ReciprocityTheory.CA.ModDepthGE.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:20.264197+00:00
-- url     : https://prove2.me/theorems/d894c558-0520-4a2c-af28-c35ec322152b
-- title:
--   Mod Depth GE: mono
-- statement:
--   The Mod Depth GE construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularAppendOfModDepthGE.lean#L10-L19

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

theorem ReciprocityTheory.CA.ModDepthGE.mono {m n : ℕ} (hmn : m ≤ n) (h : ModDepthGE R M n) : ModDepthGE R M m := by sorry
