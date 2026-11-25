-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_sum
-- name    : ReciprocityTheory.PGsh.L2.cosetCoordinates_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:28.229936+00:00
-- url     : https://prove2.me/theorems/5110e5e8-da92-49bb-9bb7-7d842a849c56
-- title:
--   L2: coset Coordinates sum
-- statement:
--   The L2 construction uses the coset Coordinates sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsFamilyValuationDetEqOne.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsFamilyValuationDetEqOne.lean#L12-L17

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFamilyValuationDetEqOne
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

theorem ReciprocityTheory.PGsh.L2.cosetCoordinates_sum (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) {ι : Type}
    [Fintype ι] (g : ι → N → C) (x : N) :
    h3co K β (∑ i, g i) x = ∑ i, h3co K β (g i) x := by sorry
