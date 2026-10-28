-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_minDelayAltLang_mem_NP
-- name    : ProjSchedTW.Complexity.minDelayAltLang_mem_NP
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:39:59.696997+00:00
-- url     : https://prove2.me/theorems/c4a560f8-3837-4e9b-862b-4857a73dc346
-- title:
--   Min-Delaying-Alternative Membership in $\text{NP}$
-- statement:
--   The decision language $\text{minDelayAltLang}$ (Proposition 2.5.4 of Neumann, Schwindt & Zimmermann, p. 48), testing whether a forbidden set $F$ admits a minimal delaying alternative $B \subseteq F$ containing a given activity $j^* \in F$, belongs to $\text{NP}$.
-- source:
--   Neumann, Schwindt & Zimmermann (2003), Project Scheduling with Time Windows and Scarce Resources, Proposition 2.5.4, p. 48

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_DelayingAlternatives

namespace ProjSchedTW.Complexity

theorem minDelayAltLang_mem_NP : minDelayAltLang ∈ CookPvsNP.NP BSym := by sorry

end ProjSchedTW.Complexity
