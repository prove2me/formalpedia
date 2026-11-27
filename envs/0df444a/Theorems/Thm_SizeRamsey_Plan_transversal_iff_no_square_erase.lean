-- Prove2me | Theorems.Thm_SizeRamsey_Plan_transversal_iff_no_square_erase
-- name    : SizeRamsey.Plan.transversal_iff_no_square_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:49.49379+00:00
-- url     : https://prove2.me/theorems/a58b3b34-7ddb-5186-b22e-8a78474852d9
-- title:
--   Plan: transversal iff no square erase
-- statement:
--   The Plan construction uses the transversal iff no square erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L214-L223
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L214-L223

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.transversal_iff_no_square_erase (D : Finset V) :
    c4Transversal G D ↔ ¬ HasC4 (erase G D) := by sorry
