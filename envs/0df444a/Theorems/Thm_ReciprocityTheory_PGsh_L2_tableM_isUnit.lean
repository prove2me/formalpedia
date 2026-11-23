-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_tableM_isUnit
-- name    : ReciprocityTheory.PGsh.L2.tableM_isUnit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:24.886637+00:00
-- url     : https://prove2.me/theorems/46bc7dc3-2a85-4967-a675-2a9cbbad3bcb
-- title:
--   L2: table M is Unit
-- statement:
--   The L2 construction uses the table M is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L18-L20

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem ReciprocityTheory.PGsh.L2.tableM_isUnit (e : H ≃ AddChar N C) (σ : H ≃ N) : IsUnit (tableM e σ).det := by sorry
