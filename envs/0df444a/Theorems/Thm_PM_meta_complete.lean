-- Prove2me | Theorems.Thm_PM_meta_complete
-- name    : PM.meta_complete
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:11:20.577745+00:00
-- url     : https://prove2.me/theorems/c5dcfea6-e2cb-403f-945e-ca472c631aff
-- title:
--   PM ✱1 (about the system): completeness of ✱1 for two-valued truth tables
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Completeness of the primitive system ✱1 of *Principia Mathematica*.**
--
--   Let $\varphi$ be a formula of PM's propositional calculus (built from propositional variables by ${\sim}$ and $\lor$; $\supset$, $\land$, $\equiv$ are PM's definitions ✱1·01, ✱3·01, ✱4·01). Call $\varphi$ a *tautology* if it is true under every assignment of truth values to the propositional variables occurring in it. Then
--
--   $$
--   \varphi \text{ is a tautology} \implies \varphi \text{ is a theorem of ✱1},
--   $$
--
--   that is, $\varphi$ is derivable from the primitive propositions ✱1·2–✱1·6 by the rule ✱1·1.
--
--   PM does not state or prove this; it is the completeness theorem for PM's propositional calculus (Post, 1921). With the soundness card it shows that the theorems of ✱1 are exactly the tautologies.
--
--   **Formalization Note** The hypothesis is the decidable check `PM.F.isTaut φ = true`, which evaluates $\varphi$ under every assignment to the list of its variables (`PM.F.vars`, `PM.assignments`).
--
--   Source: [`PM.complete`](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Complete.lean#L190-L195).
-- source:
--   About Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱1; Post (1921); formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Complete.lean#L190-L195

import Definitions.Def_PM_core_star1_system
import Definitions.Def_PM_core_statement_formulas
import Definitions.Def_PM_core_hypothetical_derivations
import Definitions.Def_PM_core_valuation_literals

open PM
open F Pf

theorem PM.meta_complete (p : F) (h : p.isTaut = true) : Thm p := by sorry
