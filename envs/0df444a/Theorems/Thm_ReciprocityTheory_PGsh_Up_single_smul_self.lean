-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_single_smul_self
-- name    : ReciprocityTheory.PGsh.Up.single_smul_self
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:37.560819+00:00
-- url     : https://prove2.me/theorems/7bc28b4d-9ed3-490f-8ed2-7a8df8f12cec
-- title:
--   Up: single smul self
-- statement:
--   The Up construction uses the single smul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemOfSumSingleEqZero.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemOfSumSingleEqZero.lean#L13-L19

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

theorem ReciprocityTheory.PGsh.Up.single_smul_self {m : ℕ} (c : Fin m → R) (i : Fin m) :
    c i • (Pi.single i (1 : R ⧸ Ideal.span {c i}) : (i : Fin m) → R ⧸ Ideal.span {c i}) = 0 := by sorry
