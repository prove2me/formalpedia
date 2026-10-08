-- Prove2me | Theorems.Thm_PriceOfStability_Harmonic_theorem3_1
-- name    : PriceOfStability.Harmonic.theorem3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:40:21.20631+00:00
-- url     : https://prove2.me/theorems/77bd74f3-b84a-4818-a82b-de074bb156b0
-- title:
--   Theorem 3.1 — cost ≤ A·Φ and Φ ≤ B·cost imply price of stability ≤ A·B
-- statement:
--   Let $G$ be a congestion game with arbitrary per-user cost functions $f_e$, let $\Phi$ be its Rosenthal potential (2.1), and let $\operatorname{cost}(S)=\sum_i c_i(S)$ be the total cost of the players. Suppose $A\ge 0$ and $B$ are real numbers such that, for every strategy profile $S$,
--   $$\operatorname{cost}(S)\le A\cdot\Phi(S)\qquad\text{and}\qquad \Phi(S)\le B\cdot\operatorname{cost}(S),$$
--   and suppose some strategy profile exists. Then the price of stability is at most $A\cdot B$: there is a pure Nash equilibrium $S$ with
--   $$\operatorname{cost}(S)\le A\cdot B\cdot\operatorname{cost}(P)\quad\text{for every strategy profile } P.$$
--
--   This is the general form of the potential-function argument; Theorems 2.1 and 2.3 are its instances with $A=1$, $B=H(k)$.
--
--   **Formalization Note.** The hypothesis $A\ge 0$ is used but not stated in the paper. The price of stability is stated as the existence of a good equilibrium, without dividing by the optimal cost. For a fair game the players' total cost equals the cost of the designed network.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1609 (PDF p. 8), Theorem 3.1; proof p. 1610 (PDF p. 9)

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 3.1, p. 1609 (PDF p. 8), proof p. 1610 (PDF p. 9): if the potential `Φ` of (2.1)
satisfies `cost(S) ≤ A · Φ(S)` and `Φ(S) ≤ B · cost(S)` for all `S`, then the price of
stability is at most `A · B`: some pure Nash equilibrium `S` has `cost(S) ≤ A · B · cost(P)`
for every strategy vector `P`.

**Formalization Note.** Stated for every congestion game with arbitrary edge functions `f_e`;
`cost(S) = Σᵢ Cᵢ(S)` is `sumCost` (for a fair game it equals the cost of the designed
network, by `shapley_budget_balance`). "All S" ranges over feasible strategy vectors. The
hypothesis `0 ≤ A` is implicit in the paper: its proof uses `A · Φ(S′) ≤ A · Φ(S*)`.
The price of stability is stated in existence form, without dividing by the optimum; the
existence of a profile (every `Σᵢ` nonempty) is assumed. -/
theorem theorem3_1 {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A B : ℝ) (hA : 0 ≤ A)
    (hcost : ∀ S, IsProfile G S → sumCost G S ≤ A * potential G S)
    (hpot : ∀ S, IsProfile G S → potential G S ≤ B * sumCost G S)
    (hP : ∃ P, IsProfile G P) :
    ∃ S, IsPureNash G S ∧ ∀ P, IsProfile G P → sumCost G S ≤ A * B * sumCost G P := by sorry

end PriceOfStability.Harmonic
