-- Prove2me | Theorems.Thm_PM_star1_3_add
-- name    : PM.star1_3_add
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:07:45.776241+00:00
-- url     : https://prove2.me/theorems/61eef44c-b429-4854-9e8e-c897266a44d3
-- title:
--   PM ✱1·3 (Add): $q \supset (p \lor q)$
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Principia Mathematica ✱1·3 (Add)**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), Part I, Section A, p. 100. PM prints (Gutenberg #78050 transcription):
--
--   $$
--   \vdash \colon q.\supset .p \lor q \qquad \text{Pp}.
--   $$
--
--   Formulas of PM's propositional calculus are built from propositional variables by negation ${\sim}$ and disjunction $\lor$, PM's two primitive ideas (✱1). Implication, conjunction and equivalence are PM's definitions: $p \supset q$ is ${\sim}p \lor q$ (✱1·01), $p \land q$ (PM writes $p\,.\,q$) is ${\sim}({\sim}p \lor {\sim}q)$ (✱3·01), and $p \equiv q$ is $(p \supset q) \land (q \supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and $p \supset q$, infer $q$).
--
--   For all formulas $p$, $q$, the formula
--
--   $$
--   q \supset (p \lor q)
--   $$
--
--   is a theorem of ✱1: it is one of PM's primitive propositions (Pp), so it is asserted outright.
--
--   PM refers to this proposition by the name **Add** (Vol. I, *Alphabetical list of propositions referred to by names*), and cites it by that name in later proofs.
--
--   **Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` (variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions (`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. The statement is the type of the constructor `PM.Thm.add`. Brackets are written out in full here in place of PM's dots.
--
--   Lean/Mathlib counterpart: [`Or.inr`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/Prelude.lean#L624) (Lean core v4.33.1). It states the same law for Lean's own propositions, connective for connective.
--
--   Source: [`PM.Thm.add` in PM/Basic.lean](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Basic.lean#L28-L28) at commit 2e43991fec42.
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱1·3, p. 100; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Basic.lean#L28-L28

import Definitions.Def_PM_core_star1_system

open PM

theorem PM.star1_3_add (p q : F) : Thm (F.imp q (.or p q)) := by sorry
