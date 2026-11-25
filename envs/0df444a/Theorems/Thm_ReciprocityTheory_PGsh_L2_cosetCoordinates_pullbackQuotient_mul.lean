-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_pullbackQuotient_mul
-- name    : ReciprocityTheory.PGsh.L2.cosetCoordinates_pullbackQuotient_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:20.678075+00:00
-- url     : https://prove2.me/theorems/dda580ff-bb8e-4b6a-b762-bcc4dc087f94
-- title:
--   L2: coset Coordinates pullback Quotient mul
-- statement:
--   The L2 construction uses the coset Coordinates pullback Quotient mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetLeOneOfEntriesIntegral.lean#L179-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetLeOneOfEntriesIntegral.lean#L179-L188

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem ReciprocityTheory.PGsh.L2.cosetCoordinates_pullbackQuotient_mul (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (e : N ⧸ K → C) (f : N → C)
    (x : N) : h3co K β (pullQ (R := R) K e * f) x = e (x : N ⧸ K) • h3co K β f x := by sorry
