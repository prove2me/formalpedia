-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_Supplement_zpp_not_subset_psp
-- name    : WatsonPseudodeterminism.MASeparation.Supplement.zpp_not_subset_psp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:32:50.824212+00:00
-- url     : https://prove2.me/theorems/0e29ce66-050c-488e-b769-3c51abeae512
-- title:
--   Theorem 1 — ZPP is not contained in psP
-- statement:
--   There exists an infinite family $F$ of two-party partial Boolean functions, on input lengths $N_t\to\infty$, that is in ZPP but not in psP:
--   $$\exists F:\quad F\in\mathrm{ZPP}\ \land\ F\notin\mathrm{psP}.$$
--   Here $F\in\mathrm{ZPP}$ means $F\in\mathrm{RP}$ and $\overline F\in\mathrm{RP}$, each with RP-type protocols (one distribution, completeness $2/3$, zero acceptance on valid 0-inputs) of cost at most $C(\lfloor\log_2N_t\rfloor+1)^C$ for one constant $C$; $F\in\mathrm{psP}$ means psP-type protocols (one distribution, acceptance in $[0,1/3]\cup[2/3,1]$ on every input, valid or invalid) of such polylogarithmic cost. The theorem is proved in the source; this item requests its formal proof.
--
--   Differences from the source:
--   - encoding: infinite families with polylog N complexity → families with lengths tending to infinity and one natural C bounding costs by C(log₂ N + 1)^C; reason: same uniform polylogarithmic convention as the base mission's classes
--   - reading: ZPP (zero-sided-error communication) → RP ∩ coRP: RP-type protocols for F and for its complement F̄; reason: the paper recalls ZPP = RP ∩ coRP on p. 2 and its §3 proof shows exactly F ∈ RP and F̄ ∈ RP
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), Theorem 1, §1, p. 2; proof §3, pp. 8–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Supplement_Classes

namespace WatsonPseudodeterminism.MASeparation.Supplement

/-- Theorem 1, p. 2: ZPP is not contained in psP in communication complexity. -/
theorem zpp_not_subset_psp :
    ∃ F : Family, InZPP F ∧ ¬ InPsP F := by sorry

end WatsonPseudodeterminism.MASeparation.Supplement
