-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_DualPair_mr_ker
-- name    : ReciprocityTheory.PGsh.DualPair.mr_ker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:18.806931+00:00
-- url     : https://prove2.me/theorems/0c3a989f-689d-49b2-8a08-43526f08a663
-- title:
--   Dual Pair: mr ker
-- statement:
--   The Dual Pair construction uses the mr ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L165-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L165-L169

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
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)

theorem ReciprocityTheory.PGsh.DualPair.mr_ker (r : (R : Type u)) :
    ∀ a ∈ Dp.π.ker, (Dp.mr r).1.toLinearMap a ∈ Dp.π.ker := by sorry
