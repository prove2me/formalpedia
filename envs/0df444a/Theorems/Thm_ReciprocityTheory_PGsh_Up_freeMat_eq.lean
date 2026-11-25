-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_freeMat_eq
-- name    : ReciprocityTheory.PGsh.Up.freeMat_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:50.971445+00:00
-- url     : https://prove2.me/theorems/4f7ba413-45df-4f0e-a2a9-fdaa3757bb9e
-- title:
--   Up: free Mat eq
-- statement:
--   The Up construction uses the free Mat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L53-L56

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
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
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem ReciprocityTheory.PGsh.Up.freeMat_eq {n : ℕ} (a : Fin n → C) (s : ℕ) :
    freeMat a s = Matrix.blockDiagonal fun _ : Fin s => Matrix.vandermonde a := by sorry
