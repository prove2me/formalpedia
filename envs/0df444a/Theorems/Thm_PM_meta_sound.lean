-- Prove2me | Theorems.Thm_PM_meta_sound
-- name    : PM.meta_sound
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:07:46.118831+00:00
-- url     : https://prove2.me/theorems/27f020cb-1917-41d3-b151-6e0ac1777adf
-- title:
--   PM ✱1 (about the system): soundness of ✱1 for two-valued truth tables
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **Soundness of the primitive system ✱1 of *Principia Mathematica*.**
--
--   Let $\varphi$ be a formula of PM's propositional calculus (built from propositional variables by ${\sim}$ and $\lor$; $\supset$, $\land$, $\equiv$ are PM's definitions ✱1·01, ✱3·01, ✱4·01). A *valuation* $v$ assigns a truth value to every propositional variable; $\llbracket\varphi\rrbracket_v$ is the truth value of $\varphi$ computed by the usual tables (${\sim}$ is negation, $\lor$ is inclusive or). If $\varphi$ is a theorem of ✱1 (derivable from ✱1·2–✱1·6 by ✱1·1), then
--
--   $$
--   \llbracket\varphi\rrbracket_v = \mathrm{true} \quad\text{for every valuation } v.
--   $$
--
--   This is not a proposition of PM; it is a result about PM's system. It turns a falsifying valuation into a proof that a formula is *not* a theorem, which is how transcription errors in the source text are detected (the card `PM.meta_perm_variant_not_thm`).
--
--   **Formalization Note** `PM.F.eval v φ : Bool` is the truth-table value; valuations are functions from variable names (strings) to `Bool`.
--
--   Source: [`PM.sound`](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Basic.lean#L39-L46).
-- source:
--   About Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱1; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Basic.lean#L39-L46

import Definitions.Def_PM_core_star1_system

open PM

theorem PM.meta_sound {p : F} (h : Thm p) : ∀ v, p.eval v = true := by sorry
