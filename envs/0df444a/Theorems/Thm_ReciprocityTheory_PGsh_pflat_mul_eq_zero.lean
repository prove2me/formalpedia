-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_pflat_mul_eq_zero
-- name    : ReciprocityTheory.PGsh.pflat_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:09:38.585442+00:00
-- url     : https://prove2.me/theorems/c6d88e2d-349e-4fc9-99fc-eb08c9bd3951
-- title:
--   PGsh: pflat mul eq zero
-- statement:
--   The PGsh construction uses the pflat mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulIterateRootEqZero.lean#L84-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulIterateRootEqZero.lean#L84-L108

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
variable {p : ℕ} [hp : Fact p.Prime] {O : Type*} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem ReciprocityTheory.PGsh.pflat_mul_eq_zero (hO : ∀ x : O, (p : O) * x = 0 → x = 0) (pflat : PreTilt O p)
    (hpf : pflat.untilt = (p : O)) (x : PreTilt O p) (hx : pflat * x = 0) : x = 0 := by sorry
