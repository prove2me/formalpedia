-- Prove2me | Theorems.Thm_PM_star5_17
-- name    : PM.star5_17
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:11:02.533837+00:00
-- url     : https://prove2.me/theorems/f00f7de9-256f-482c-b558-1b48bd942b45
-- title:
--   PM ✱5·17: $((p \lor q) \land {\sim} (p \land q)) \equiv (p \equiv {\sim} q)$
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Principia Mathematica ✱5·17**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), Part I, Section A, p. 129. PM prints (Gutenberg #78050 transcription):
--
--   $$
--   \vdash:p\lor q.{\sim}(p.q).\equiv .p\equiv {\sim}q
--   $$
--
--   Formulas of PM's propositional calculus are built from propositional variables by negation ${\sim}$ and disjunction $\lor$, PM's two primitive ideas (✱1). Implication, conjunction and equivalence are PM's definitions: $p \supset q$ is ${\sim}p \lor q$ (✱1·01), $p \land q$ (PM writes $p\,.\,q$) is ${\sim}({\sim}p \lor {\sim}q)$ (✱3·01), and $p \equiv q$ is $(p \supset q) \land (q \supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and $p \supset q$, infer $q$).
--
--   For all formulas $p$, $q$, the formula
--
--   $$
--   ((p \lor q) \land {\sim} (p \land q)) \equiv (p \equiv {\sim} q)
--   $$
--
--   is a theorem of ✱1.
--
--   It is one of the propositions of ✱5 from which PM builds the propositional calculus used throughout the work.
--
--   **Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` (variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions (`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. The statement formula is the definition `PM.s5_17` of the bundle `PM_core_statement_formulas`. Brackets are written out in full here in place of PM's dots.
--
--   Source: [`PM.t5_17` in PM/Replay2.lean](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay2.lean#L724-L731) at commit 2e43991fec42.
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱5·17, p. 129; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay2.lean#L724-L731

import Definitions.Def_PM_core_star1_system
import Definitions.Def_PM_core_statement_formulas
import Definitions.Def_PM_core_hypothetical_derivations

open PM
open F Pf

theorem PM.star5_17 (p : F) (q : F) : Thm (s5_17 p q) := by sorry
