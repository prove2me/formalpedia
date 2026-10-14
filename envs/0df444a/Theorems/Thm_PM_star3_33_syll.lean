-- Prove2me | Theorems.Thm_PM_star3_33_syll
-- name    : PM.star3_33_syll
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:09:48.959505+00:00
-- url     : https://prove2.me/theorems/4fd36df4-6cfc-4fe9-8ecd-fce42adf1e13
-- title:
--   PM ✱3·33 (Syll): $((p \supset q) \land (q \supset r)) \supset (p \supset r)$
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Principia Mathematica ✱3·33 (Syll)**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), Part I, Section A, p. 118. PM prints (Gutenberg #78050 transcription):
--
--   $$
--   \vdash :p\supset q .q\supset r. \supset .p\supset r
--   $$
--
--   Formulas of PM's propositional calculus are built from propositional variables by negation ${\sim}$ and disjunction $\lor$, PM's two primitive ideas (✱1). Implication, conjunction and equivalence are PM's definitions: $p \supset q$ is ${\sim}p \lor q$ (✱1·01), $p \land q$ (PM writes $p\,.\,q$) is ${\sim}({\sim}p \lor {\sim}q)$ (✱3·01), and $p \equiv q$ is $(p \supset q) \land (q \supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and $p \supset q$, infer $q$).
--
--   For all formulas $p$, $q$, $r$, the formula
--
--   $$
--   ((p \supset q) \land (q \supset r)) \supset (p \supset r)
--   $$
--
--   is a theorem of ✱1.
--
--   PM refers to this proposition by the name **Syll** (Vol. I, *Alphabetical list of propositions referred to by names*), and cites it by that name in later proofs.
--
--   **Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` (variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions (`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. The statement formula is the definition `PM.s3_33` of the bundle `PM_core_statement_formulas`. Brackets are written out in full here in place of PM's dots.
--
--   Source: [`PM.t3_33` in PM/Replay.lean](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay.lean#L277-L279) at commit 2e43991fec42.
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱3·33, p. 118; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay.lean#L277-L279

import Definitions.Def_PM_core_star1_system
import Definitions.Def_PM_core_statement_formulas

open PM
open F

theorem PM.star3_33_syll (p : F) (q : F) (r : F) : Thm (s3_33 p q r) := by sorry
