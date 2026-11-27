-- Prove2me | Theorems.Thm_SizeRamsey_Plan_square_supported_no_bridge
-- name    : SizeRamsey.Plan.square_supported_no_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:26:12.346003+00:00
-- url     : https://prove2.me/theorems/b3e324de-0ca7-5e73-aeeb-b172acc952b5
-- title:
--   Plan: square supported no bridge
-- statement:
--   The Plan construction uses the square supported no bridge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L141-L163
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L141-L163

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.square_supported_no_bridge
    (h : SquareSupported G) {u v : V} (huv : G.Adj u v) :
    ¬ G.IsBridge s(u, v) := by sorry
