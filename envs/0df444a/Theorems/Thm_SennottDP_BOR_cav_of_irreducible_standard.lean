-- Prove2me | Theorems.Thm_SennottDP_BOR_cav_of_irreducible_standard
-- name    : SennottDP.BOR.cav_of_irreducible_standard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:30:26.245031+00:00
-- url     : https://prove2.me/theorems/174d7ae3-781b-4370-9651-aebbb2cf8f7e
-- title:
--   Corollary 7.5.10 — (CAV*) implies (CAV), hence (BOR)
-- statement:
--   Assume the (CAV*) assumptions: (CAV*1) there is a standard policy $d$ — $z$ standard for a state $z$ — whose positive recurrent class is all of $S$, $R_d=S$; (CAV*2) for every $U>0$ the set $D_U=\{i\mid C(i,a)\le U\text{ for some }a\}$ is finite. Then the (CAV) assumptions hold for $z$ and $d$, and hence (BOR) is valid for $z$, $d$ and some $\varepsilon>0$.
--
--   **Formalization Note** "Standard" is read as "$z$ standard for some state $z$"; the conclusion is stated for that same $z$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 149, Corollary 7.5.10

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Corollary 7.5.10, p. 149. Assume (CAV*): (CAV*1) there is a standard policy
`d` (here: `z` standard for the state `z`) with `R_d = S`; (CAV*2) for every `U > 0` the set
`D_U = {i | C(i,a) ≤ U for some a}` is finite. Then the (CAV) assumptions hold, and hence (BOR)
is valid (for `z`, `d` and some `ε > 0`). -/
theorem cav_of_irreducible_standard {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (d : RandStationaryPolicy M) (hd : IsZStandard d.toPolicy z)
    (hR : recClass M d z = Set.univ)
    (hD : ∀ U : ℝ, 0 < U → (lowCostSet M (ENNReal.ofReal U)).Finite) :
    CAVAssumptions M z d ∧ ∃ ε : ℝ, BORAssumptions M z d ε := by sorry

end SennottDP.BOR
