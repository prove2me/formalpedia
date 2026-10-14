-- Prove2me | Theorems.Thm_PM_star3_11
-- name    : PM.star3_11
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:09:36.438867+00:00
-- url     : https://prove2.me/theorems/237c6c4e-d7f6-4c16-97f6-222fff28f386
-- title:
--   PM ✱3·11: ${\sim} ({\sim} p \lor {\sim} q) \supset (p \land q)$
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Principia Mathematica ✱3·11**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), Part I, Section A, p. 116. PM prints (Gutenberg #78050 transcription):
--
--   $$
--   \vdash : {\sim} ({\sim} p \lor {\sim} q) . \supset . p . q
--   $$
--
--   Formulas of PM's propositional calculus are built from propositional variables by negation ${\sim}$ and disjunction $\lor$, PM's two primitive ideas (✱1). Implication, conjunction and equivalence are PM's definitions: $p \supset q$ is ${\sim}p \lor q$ (✱1·01), $p \land q$ (PM writes $p\,.\,q$) is ${\sim}({\sim}p \lor {\sim}q)$ (✱3·01), and $p \equiv q$ is $(p \supset q) \land (q \supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and $p \supset q$, infer $q$).
--
--   For all formulas $p$, $q$, the formula
--
--   $$
--   {\sim} ({\sim} p \lor {\sim} q) \supset (p \land q)
--   $$
--
--   is a theorem of ✱1.
--
--   It is one of the propositions of ✱3 from which PM builds the propositional calculus used throughout the work.
--
--   **Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` (variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions (`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. The statement formula is the definition `PM.s3_11` of the bundle `PM_core_statement_formulas`. Brackets are written out in full here in place of PM's dots.
--
--   Source: [`PM.t3_11` in PM/Replay.lean](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay.lean#L233-L235) at commit 2e43991fec42.
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱3·11, p. 116; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay.lean#L233-L235

import Definitions.Def_PM_core_star1_system
import Definitions.Def_PM_core_statement_formulas

open PM
open F

theorem PM.star3_11 (p : F) (q : F) : Thm (s3_11 p q) := by sorry
