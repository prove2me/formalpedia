-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_det_freeMat
-- name    : ReciprocityTheory.PGsh.Up.det_freeMat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:05.8738+00:00
-- url     : https://prove2.me/theorems/6c7e7807-e488-4ac0-945a-36b9425d43d9
-- title:
--   Up: det free Mat
-- statement:
--   The Up construction uses the det free Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L58-L60

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

theorem ReciprocityTheory.PGsh.Up.det_freeMat {n : ℕ} (a : Fin n → C) (s : ℕ) :
    (freeMat a s).det = (Matrix.vandermonde a).det ^ s := by sorry
