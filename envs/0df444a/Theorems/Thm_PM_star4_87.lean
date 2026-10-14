-- Prove2me | Theorems.Thm_PM_star4_87
-- name    : PM.star4_87
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:10:46.813062+00:00
-- url     : https://prove2.me/theorems/3b23c4df-d7b5-4065-98f4-f784aa34550b
-- title:
--   PM ✱4·87: ((((p ∧ q) ⊃ r) ≡ (p ⊃ (q ⊃ r))) ∧ ((p ⊃ (q ⊃ r)) ≡ (q ⊃ (p ⊃ r)))) ∧ ((q ⊃ (p ⊃ r)) ≡ ((q ∧ p) ⊃ r))
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Principia Mathematica ✱4·87**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), Part I, Section A, p. 127. PM prints (Gutenberg #78050 transcription):
--
--   $$
--   \begin{aligned}\vdash\colon\ldotp p.q.\supset .r:\equiv:p.\supset .q\supset &r:\equiv:q.\supset .p\supset r:\equiv:q.p.\supset .r\\ &\quad[\text{Exp. Comm. Imp}]\end{aligned}
--   $$
--
--   Formulas of PM's propositional calculus are built from propositional variables by negation ${\sim}$ and disjunction $\lor$, PM's two primitive ideas (✱1). Implication, conjunction and equivalence are PM's definitions: $p \supset q$ is ${\sim}p \lor q$ (✱1·01), $p \land q$ (PM writes $p\,.\,q$) is ${\sim}({\sim}p \lor {\sim}q)$ (✱3·01), and $p \equiv q$ is $(p \supset q) \land (q \supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and $p \supset q$, infer $q$).
--
--   For all formulas $p$, $q$, $r$, the formula
--
--   $$
--   ((((p \land q) \supset r) \equiv (p \supset (q \supset r))) \land ((p \supset (q \supset r)) \equiv (q \supset (p \supset r)))) \land ((q \supset (p \supset r)) \equiv ((q \land p) \supset r))
--   $$
--
--   is a theorem of ✱1.
--
--   It is one of the propositions of ✱4 from which PM builds the propositional calculus used throughout the work.
--
--   **Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` (variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions (`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. The statement formula is the definition `PM.s4_87` of the bundle `PM_core_statement_formulas`. Brackets are written out in full here in place of PM's dots.
--
--   Source: [`PM.t4_87` in PM/Replay2.lean](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay2.lean#L691-L694) at commit 2e43991fec42.
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱4·87, p. 127; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay2.lean#L691-L694

import Definitions.Def_PM_core_star1_system
import Definitions.Def_PM_core_statement_formulas
import Definitions.Def_PM_core_hypothetical_derivations

open PM
open F Pf

theorem PM.star4_87 (p : F) (q : F) (r : F) : Thm (s4_87 p q r) := by sorry
