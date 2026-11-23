-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_untilt_eq_of_coeff
-- name    : ReciprocityTheory.PGsh.untilt_eq_of_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:36.301305+00:00
-- url     : https://prove2.me/theorems/d84e822b-3a0a-4684-a244-88e163ff0b84
-- title:
--   PGsh: untilt eq of coeff
-- statement:
--   The PGsh construction uses the untilt eq of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsPrimitiveRoot.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsPrimitiveRoot.lean#L22-L26

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

theorem ReciprocityTheory.PGsh.untilt_eq_of_coeff (x : PreTilt O p) (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n)
    (hx : ∀ n, Perfection.coeff (ModP O p) p n x = Ideal.Quotient.mk (span {(p : O)}) (f n)) :
    x.untilt = f 0 := by sorry
