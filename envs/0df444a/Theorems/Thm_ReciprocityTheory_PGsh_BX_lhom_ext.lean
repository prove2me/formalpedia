-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_lhom_ext
-- name    : ReciprocityTheory.PGsh.BX.lhom_ext
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:39.741356+00:00
-- url     : https://prove2.me/theorems/046ce514-5dee-5ec7-891e-2907e54752a5
-- title:
--   BX: lhom ext
-- statement:
--   The BX construction uses the lhom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsHeightUnique.lean#L18-L19

import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
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
variable (B : BX R₀)

theorem ReciprocityTheory.PGsh.BX.lhom_ext {R S : LAlg R₀} {f g : LHom R S} (h : ∀ x, f.1 x = g.1 x) : f = g := by sorry
