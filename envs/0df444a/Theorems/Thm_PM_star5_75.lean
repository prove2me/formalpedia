-- Prove2me | Theorems.Thm_PM_star5_75
-- name    : PM.star5_75
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:11:19.997189+00:00
-- url     : https://prove2.me/theorems/48c88a1f-e2a3-41a5-88ca-e526a9120897
-- title:
--   PM ✱5·75: $((r \supset {\sim} q) \land (p \equiv (q \lor r))) \supset ((p \land {\sim} q) \equiv r)$
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Principia Mathematica ✱5·75**: Whitehead and Russell, *Principia Mathematica*, Vol. I (1910), Part I, Section A, p. 131. PM prints (Gutenberg #78050 transcription):
--
--   $$
--   \vdash\colon\ldotp r\supset {\sim}q:p.\equiv .q\lor r:\supset :p.{\sim}q.\equiv .r
--   $$
--
--   Formulas of PM's propositional calculus are built from propositional variables by negation ${\sim}$ and disjunction $\lor$, PM's two primitive ideas (✱1). Implication, conjunction and equivalence are PM's definitions: $p \supset q$ is ${\sim}p \lor q$ (✱1·01), $p \land q$ (PM writes $p\,.\,q$) is ${\sim}({\sim}p \lor {\sim}q)$ (✱3·01), and $p \equiv q$ is $(p \supset q) \land (q \supset p)$ (✱4·01). A *theorem of ✱1* is a formula derivable from the primitive propositions ✱1·2–✱1·6 by the rule of inference ✱1·1 (from $p$ and $p \supset q$, infer $q$).
--
--   For all formulas $p$, $q$, $r$, the formula
--
--   $$
--   ((r \supset {\sim} q) \land (p \equiv (q \lor r))) \supset ((p \land {\sim} q) \equiv r)
--   $$
--
--   is a theorem of ✱1.
--
--   It is one of the propositions of ✱5 from which PM builds the propositional calculus used throughout the work.
--
--   **Formalization Note** Deep embedding of PM ✱1: formulas are the inductive type `PM.F` (variables named by strings), the theorems of ✱1 are the inductive predicate `PM.Thm`, whose constructors are ✱1·1–✱1·6, and ✱1·01, ✱3·01, ✱4·01 are reducible definitions (`F.imp`, `F.and`, `F.iff`), so PM's definitions hold by definition. The statement formula is the definition `PM.s5_75` of the bundle `PM_core_statement_formulas`. Brackets are written out in full here in place of PM's dots.
--
--   Source: [`PM.t5_75` in PM/Replay2.lean](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay2.lean#L1110-L1116) at commit 2e43991fec42.
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱5·75, p. 131; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Replay2.lean#L1110-L1116

import Definitions.Def_PM_core_star1_system
import Definitions.Def_PM_core_statement_formulas
import Definitions.Def_PM_core_hypothetical_derivations

open PM
open F Pf

theorem PM.star5_75 (p : F) (q : F) (r : F) : Thm (s5_75 p q r) := by sorry
