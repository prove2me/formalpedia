-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_hext_tmul
-- name    : ReciprocityTheory.PGsh.hext_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:47.467152+00:00
-- url     : https://prove2.me/theorems/16ea2ca4-b28c-4cc0-a2e3-8df7084a08fb
-- title:
--   PGsh: hext tmul
-- statement:
--   The PGsh construction uses the hext tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L173-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L173-L175

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]

theorem ReciprocityTheory.PGsh.hext_tmul (B : BX R₀) {R : LAlg R₀} (h : B.gg →ₗ[R₀] (R : Type u)) (w : B.gg) (r : (R : Type u)) :
    hext B h (w ⊗ₜ r) = h w * r := by sorry
