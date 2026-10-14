-- Prove2me | Theorems.Thm_PM_star4_13
-- name    : PM.star4_13
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:09:54.1281+00:00
-- url     : https://prove2.me/theorems/68ac8c04-7e40-4385-ac8d-73b2343ebdb2
-- title:
--   PM ✱4·13: $p \equiv {\sim} {\sim} p$
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Principia Mathematica ✱4·13**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), Part I, Section A, p. 122. PM prints (Gutenberg #78050 transcription):
--
--   $$
--   \vdash.p\equiv{\sim}({\sim} p)      \quad\text{[*2·12·14}]
--   $$
--
--   Formulas of PM's propositional calculus are built from propositional variables by negation ${\sim}$ and disjunction $\lor$, PM's two primitive ideas (✱1). Implication, conjunction and equivalence are PM's definitions: $p \supset q$ is ${\sim}p \lor q$ (✱1·01), $p \land q$ (PM writes $p\,.\,q$) is ${\sim}({\sim}p \lor {\sim}q)$ (✱3·01), and $p \equiv q$ is $(p \supset q) \land (q \supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and $p \supset q$, infer $q$).
--
--   For every formula $p$, the formula
--
--   $$
--   p \equiv {\sim} {\sim} p
--   $$
--
--   is a theorem of ✱1.
--
--   PM's Introduction lists it as the law of double negation, among "the most important of the elementary properties of propositions appearing among the deductions".
--
--   **Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` (variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions (`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. The statement formula is the definition `PM.s4_13` of the bundle `PM_core_statement_formulas`. Brackets are written out in full here in place of PM's dots.
--
--   Lean/Mathlib counterpart: [`Classical.not_not`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/Classical.lean#L144) (Lean core v4.33.1; its proof is classical; with the two sides of an equivalence the other way round). It states the same law for Lean's own propositions, connective for connective.
--
--   Source: [`PM.t4_13` in PM/Replay.lean](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay.lean#L309-L311) at commit 2e43991fec42.
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱4·13, p. 122; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay.lean#L309-L311

import Definitions.Def_PM_core_star1_system
import Definitions.Def_PM_core_statement_formulas

open PM
open F

theorem PM.star4_13 (p : F) : Thm (s4_13 p) := by sorry
