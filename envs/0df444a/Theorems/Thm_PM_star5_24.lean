-- Prove2me | Theorems.Thm_PM_star5_24
-- name    : PM.star5_24
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:11:05.248534+00:00
-- url     : https://prove2.me/theorems/247a6562-2932-44c2-a8a4-58467f2c1607
-- title:
--   PM ✱5·24: ${\sim} ((p \land q) \lor ({\sim} p \land {\sim} q)) \equiv ((p \land {\sim} q) \lor (q \land {\sim} p))$
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Principia Mathematica ✱5·24**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), Part I, Section A, p. 130. PM prints (Gutenberg #78050 transcription):
--
--   $$
--   \vdash\colon\ldotp {\sim}(p.q.\lor .{\sim}p.{\sim}q).\equiv :p.{\sim}q.\lor .q.{\sim}p
--   $$
--
--   Formulas of PM's propositional calculus are built from propositional variables by negation ${\sim}$ and disjunction $\lor$, PM's two primitive ideas (✱1). Implication, conjunction and equivalence are PM's definitions: $p \supset q$ is ${\sim}p \lor q$ (✱1·01), $p \land q$ (PM writes $p\,.\,q$) is ${\sim}({\sim}p \lor {\sim}q)$ (✱3·01), and $p \equiv q$ is $(p \supset q) \land (q \supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and $p \supset q$, infer $q$).
--
--   For all formulas $p$, $q$, the formula
--
--   $$
--   {\sim} ((p \land q) \lor ({\sim} p \land {\sim} q)) \equiv ((p \land {\sim} q) \lor (q \land {\sim} p))
--   $$
--
--   is a theorem of ✱1.
--
--   It is one of the propositions of ✱5 from which PM builds the propositional calculus used throughout the work.
--
--   **Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` (variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions (`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. The statement formula is the definition `PM.s5_24` of the bundle `PM_core_statement_formulas`. Brackets are written out in full here in place of PM's dots.
--
--   Source: [`PM.t5_24` in PM/Replay2.lean](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay2.lean#L780-L787) at commit 2e43991fec42.
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱5·24, p. 130; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay2.lean#L780-L787

import Definitions.Def_PM_core_star1_system
import Definitions.Def_PM_core_statement_formulas
import Definitions.Def_PM_core_hypothetical_derivations

open PM
open F Pf

theorem PM.star5_24 (p : F) (q : F) : Thm (s5_24 p q) := by sorry
