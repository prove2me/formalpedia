-- Prove2me | Theorems.Thm_PM_star1_2_taut
-- name    : PM.star1_2_taut
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:07:44.055213+00:00
-- url     : https://prove2.me/theorems/cae4fa0f-9d38-4c47-a6a0-316f40625547
-- title:
--   PM ✱1·2 (Taut): $(p \lor p) \supset p$
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Principia Mathematica ✱1·2 (Taut)**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), Part I, Section A, p. 100. PM prints (Gutenberg #78050 transcription):
--
--   $$
--   \vdash \colon p \lor p.\supset.p \quad \text{Pp}.
--   $$
--
--   Formulas of PM's propositional calculus are built from propositional variables by negation ${\sim}$ and disjunction $\lor$, PM's two primitive ideas (✱1). Implication, conjunction and equivalence are PM's definitions: $p \supset q$ is ${\sim}p \lor q$ (✱1·01), $p \land q$ (PM writes $p\,.\,q$) is ${\sim}({\sim}p \lor {\sim}q)$ (✱3·01), and $p \equiv q$ is $(p \supset q) \land (q \supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and $p \supset q$, infer $q$).
--
--   For every formula $p$, the formula
--
--   $$
--   (p \lor p) \supset p
--   $$
--
--   is a theorem of ✱1: it is one of PM's primitive propositions (Pp), so it is asserted outright.
--
--   PM refers to this proposition by the name **Taut** (Vol. I, *Alphabetical list of propositions referred to by names*), and cites it by that name in later proofs.
--
--   **Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` (variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions (`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. The statement is the type of the constructor `PM.Thm.taut`. Brackets are written out in full here in place of PM's dots.
--
--   Source: [`PM.Thm.taut` in PM/Basic.lean](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Basic.lean#L27-L27) at commit 2e43991fec42.
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱1·2, p. 100; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Basic.lean#L27-L27

import Definitions.Def_PM_core_star1_system

open PM

theorem PM.star1_2_taut (p : F) : Thm (F.imp (.or p p) p) := by sorry
