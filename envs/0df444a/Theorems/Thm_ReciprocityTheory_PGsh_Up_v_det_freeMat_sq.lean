-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_v_det_freeMat_sq
-- name    : ReciprocityTheory.PGsh.Up.v_det_freeMat_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:56.24521+00:00
-- url     : https://prove2.me/theorems/db452858-e27d-4ed2-9076-9e15c1070537
-- title:
--   Up: v det free Mat sq
-- statement:
--   The Up construction uses the v det free Mat sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L97-L99

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

theorem ReciprocityTheory.PGsh.Up.v_det_freeMat_sq {n : ℕ} (a : Fin n → C) (s : ℕ) :
    v (freeMat a s).det ^ 2 = v (discr a) ^ s := by sorry
