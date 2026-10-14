-- Prove2me | Theorems.Thm_PM_star1_4_perm
-- name    : PM.star1_4_perm
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:07:47.171888+00:00
-- url     : https://prove2.me/theorems/b986460e-8e50-48b8-850f-21335e7d2698
-- title:
--   PM ✱1·4 (Perm): $(p \lor q) \supset (q \lor p)$
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Principia Mathematica ✱1·4 (Perm)**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), Part I, Section A, p. 100. PM prints (Gutenberg #78050 transcription):
--
--   $$
--   \vdash \colon p \lor q.\supset.p \lor p \qquad \text{Pp}.
--   $$
--
--   Formulas of PM's propositional calculus are built from propositional variables by negation ${\sim}$ and disjunction $\lor$, PM's two primitive ideas (✱1). Implication, conjunction and equivalence are PM's definitions: $p \supset q$ is ${\sim}p \lor q$ (✱1·01), $p \land q$ (PM writes $p\,.\,q$) is ${\sim}({\sim}p \lor {\sim}q)$ (✱3·01), and $p \equiv q$ is $(p \supset q) \land (q \supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and $p \supset q$, infer $q$).
--
--   For all formulas $p$, $q$, the formula
--
--   $$
--   (p \lor q) \supset (q \lor p)
--   $$
--
--   is a theorem of ✱1: it is one of PM's primitive propositions (Pp), so it is asserted outright.
--
--   The Gutenberg transcription prints the consequent as $p \lor p$; the 1910 print has $q \lor p$, which is what is stated here. The transcribed variant is not a theorem (the card `PM.meta_perm_variant_not_thm`).
--
--   PM refers to this proposition by the name **Perm** (Vol. I, *Alphabetical list of propositions referred to by names*), and cites it by that name in later proofs.
--
--   **Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` (variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions (`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. The statement is the type of the constructor `PM.Thm.perm`. Brackets are written out in full here in place of PM's dots.
--
--   Lean/Mathlib counterpart: [`Or.symm`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/Core.lean#L1065) (Lean core v4.33.1). It states the same law for Lean's own propositions, connective for connective.
--
--   Source: [`PM.Thm.perm` in PM/Basic.lean](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Basic.lean#L29-L29) at commit 2e43991fec42.
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱1·4, p. 100; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Basic.lean#L29-L29

import Definitions.Def_PM_core_star1_system

open PM

theorem PM.star1_4_perm (p q : F) : Thm (F.imp (.or p q) (.or q p)) := by sorry
