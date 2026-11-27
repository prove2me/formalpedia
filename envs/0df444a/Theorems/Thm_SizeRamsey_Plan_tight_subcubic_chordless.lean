-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tight_subcubic_chordless
-- name    : SizeRamsey.Plan.tight_subcubic_chordless
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:25.220313+00:00
-- url     : https://prove2.me/theorems/cf4832e0-4bc8-4b22-8180-ef4d30f0d39e
-- title:
--   Plan: tight subcubic chordless
-- statement:
--   The Plan construction uses the tight subcubic chordless property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Common.lean#L32-L46
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Common.lean#L32-L46

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Equality_Common
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.tight_subcubic_chordless
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (ht : Tight G)
    (hmax : ∀ v, G.degree v ≤ 3)
    (f : Fin 4 → V) (hf : IsC4Map G f) :
    ¬ G.Adj (f 0) (f 2) ∧
    ¬ G.Adj (f 1) (f 3) := by sorry
