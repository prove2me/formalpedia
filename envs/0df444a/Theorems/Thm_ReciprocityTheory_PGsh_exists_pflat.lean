-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_exists_pflat
-- name    : ReciprocityTheory.PGsh.exists_pflat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:32.33983+00:00
-- url     : https://prove2.me/theorems/43bf9387-c235-43e5-b70d-1bf0dbd1e275
-- title:
--   PGsh: exists pflat
-- statement:
--   The PGsh construction uses the exists pflat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsPrimitiveRoot.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsPrimitiveRoot.lean#L84-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime]
variable (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C]
variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem ReciprocityTheory.PGsh.exists_pflat (hv : v.Integers O) : ∃ pflat : PreTilt O p, pflat.untilt = (p : O) := by sorry
