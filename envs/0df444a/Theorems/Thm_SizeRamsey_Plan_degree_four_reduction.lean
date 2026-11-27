-- Prove2me | Theorems.Thm_SizeRamsey_Plan_degree_four_reduction
-- name    : SizeRamsey.Plan.degree_four_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:59.609223+00:00
-- url     : https://prove2.me/theorems/f6d523e7-5ae4-5248-bd47-6b0a87811dcf
-- title:
--   Plan: degree four reduction
-- statement:
--   The Plan construction uses the degree four reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L92-L100
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L92-L100

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.degree_four_reduction
    (v : V) (hdeg : 4 ≤ G.degree v) :
    tau4 G ≤ tau4 (erase G {v}) + 1 ∧
    edgeCount (erase G {v}) + 4 ≤ edgeCount G := by sorry
