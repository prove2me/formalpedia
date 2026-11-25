-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_eq_sum_single
-- name    : ReciprocityTheory.PGsh.Up.eq_sum_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:34.798749+00:00
-- url     : https://prove2.me/theorems/40648fbc-c862-4a2c-80db-69fb5d81df59
-- title:
--   Up: eq sum single
-- statement:
--   The Up construction uses the eq sum single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemOfSumSingleEqZero.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemOfSumSingleEqZero.lean#L21-L26

import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.PGsh.Up.eq_sum_single {m : ℕ} (c : Fin m → R) (x : (i : Fin m) → R ⧸ Ideal.span {c i}) :
    x = ∑ i, (Quotient.out (x i) : R) • (Pi.single i (1 : R ⧸ Ideal.span {c i}) :
      (i : Fin m) → R ⧸ Ideal.span {c i}) := by sorry
