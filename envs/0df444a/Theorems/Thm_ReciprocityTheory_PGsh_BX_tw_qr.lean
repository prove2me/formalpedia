-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_tw_qr
-- name    : ReciprocityTheory.PGsh.BX.tw_qr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:23.041108+00:00
-- url     : https://prove2.me/theorems/d8644263-122a-4ce2-b891-dc9aae0b74ae
-- title:
--   BX: tw qr
-- statement:
--   The BX construction uses the tw qr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsLimTensor.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsLimTensor.lean#L23-L27

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor
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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {p : ℕ}

theorem ReciprocityTheory.PGsh.BX.tw_qr (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.r n).comp (Tw.q (n + 1)) = Tw.q n := by sorry
