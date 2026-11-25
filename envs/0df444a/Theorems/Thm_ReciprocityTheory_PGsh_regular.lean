-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_regular
-- name    : ReciprocityTheory.PGsh.regular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:05.976126+00:00
-- url     : https://prove2.me/theorems/696e021b-2471-424f-88e5-11be391910cb
-- title:
--   PGsh: regular
-- statement:
--   The PGsh construction uses the regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulIterateRootEqZero.lean#L117-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulIterateRootEqZero.lean#L117-L138

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MulIterateRootEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem ReciprocityTheory.PGsh.regular (hO : ∀ x : O, (p : O) * x = 0 → x = 0) : RegularStatement p O := by sorry
