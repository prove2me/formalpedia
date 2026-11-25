-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_colength_sq_blockVandermonde
-- name    : ReciprocityTheory.PGsh.Up.colength_sq_blockVandermonde
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:49.965956+00:00
-- url     : https://prove2.me/theorems/6ef78a70-592f-47be-89a0-f3539d415d2e
-- title:
--   Up: colength sq block Vandermonde
-- statement:
--   The Up construction uses the colength sq block Vandermonde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L101-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L101-L108

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

theorem ReciprocityTheory.PGsh.Up.colength_sq_blockVandermonde {n : ℕ} (a : Fin n → C) (s : ℕ) (F S : Lat v (Fin n × Fin s))
    (hF : F.B = freeMat a s) (hS : S.pts = sumPts (fun _ => Lat.std v (Fin s))) :
    colen F S ^ 2 = v (discr a) ^ s := by sorry
