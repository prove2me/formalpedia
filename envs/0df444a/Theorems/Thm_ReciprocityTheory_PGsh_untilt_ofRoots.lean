-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_untilt_ofRoots
-- name    : ReciprocityTheory.PGsh.untilt_ofRoots
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:29.008792+00:00
-- url     : https://prove2.me/theorems/460207bb-0200-48d5-b511-298c1c8ecfa6
-- title:
--   PGsh: untilt of Roots
-- statement:
--   The PGsh construction uses the untilt of Roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsPrimitiveRoot.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsPrimitiveRoot.lean#L37-L39

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
variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem ReciprocityTheory.PGsh.untilt_ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) :
    (ofRoots f hf).untilt = f 0 := by sorry
