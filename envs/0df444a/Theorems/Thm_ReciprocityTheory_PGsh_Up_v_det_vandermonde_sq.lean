-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_v_det_vandermonde_sq
-- name    : ReciprocityTheory.PGsh.Up.v_det_vandermonde_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:12.842731+00:00
-- url     : https://prove2.me/theorems/86d6c48d-87c9-5e77-962b-305dec06416e
-- title:
--   Up: v det vandermonde sq
-- statement:
--   The Up construction uses the v det vandermonde sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L62-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L62-L95

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

theorem ReciprocityTheory.PGsh.Up.v_det_vandermonde_sq {n : ℕ} (a : Fin n → C) :
    v (Matrix.vandermonde a).det ^ 2 = v (discr a) := by sorry
