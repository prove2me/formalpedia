-- Prove2me | Theorems.Thm_PM_meta_perm_variant_not_thm
-- name    : PM.meta_perm_variant_not_thm
-- status  : Proved
-- author  : @AA
-- created : 2026-10-13T16:07:47.745361+00:00
-- url     : https://prove2.me/theorems/d2b2dd6d-dfaf-4159-b937-59299839d9f6
-- title:
--   PM ✱1·4 (about the text): the transcribed $p \lor q \supset p \lor p$ is not a theorem of ✱1
-- statement:
--   **DRAFT** — part of an in-progress public formalization of *Principia Mathematica*; it may still change, and every change is dated in the project's [change log](https://github.com/willmcginnis/principia-mathematica-lean/blob/main/docs/EXPORT_LOG.md).
--
--   **A check on the text of ✱1·4 (Perm).** PM's primitive proposition ✱1·4 is, in the 1910 print (Vol. I, p. 100),
--
--   $$
--   (p \lor q) \supset (q \lor p).
--   $$
--
--   The Gutenberg #78050 transcription prints $p \lor p$ in place of $q \lor p$. Let $p$ and $q$ be two distinct propositional variables. Then the transcribed formula
--
--   $$
--   (p \lor q) \supset (p \lor p)
--   $$
--
--   is **not** a theorem of ✱1 (not derivable from ✱1·2–✱1·6 by ✱1·1, with the 1910 ✱1·4).
--
--   This records, as a checked fact, that the one-letter variant is a transcription slip and not a reading of PM: the card for ✱1·4 follows the print.
--
--   **Formalization Note** $p$ and $q$ are the variables named "p" and "q" (`F.var "p"`, `F.var "q"`), introduced by local notation.
--
--   Source: [`PM.star1_4_variant_not_a_theorem`](https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Star2.lean#L11-L15).
-- source:
--   Whitehead and Russell, Principia Mathematica, Vol. I (1910), ✱1·4, p. 100; Project Gutenberg eBook #78050; formalization: https://github.com/willmcginnis/principia-mathematica-lean/blob/2e43991fec4221198853c15ba637b6c8430cec4b/PM/Star2.lean#L11-L15

import Definitions.Def_PM_core_star1_system

open PM
open F
local notation "p" => F.var "p"
local notation "q" => F.var "q"
local notation "r" => F.var "r"

theorem PM.meta_perm_variant_not_thm : ¬ Thm (imp (.or p q) (.or p p)) := by sorry
