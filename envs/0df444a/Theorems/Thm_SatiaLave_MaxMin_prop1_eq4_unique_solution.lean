-- Prove2me | Theorems.Thm_SatiaLave_MaxMin_prop1_eq4_unique_solution
-- name    : SatiaLave.MaxMin.prop1_eq4_unique_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:38:34.404353+00:00
-- url     : https://prove2.me/theorems/bd0e3acc-0479-4efc-ad8a-b73e78aafce2
-- title:
--   Proposition 1 — the equations (4) have a unique solution, the max-min return
-- statement:
--   Let $T$ be the operator of equations (4): for a value vector $v$ and a state $j$,
--   $$(Tv)_j=\sup_{\tau}\ \sum_{k}\tau_k\ \inf_{\alpha}\ \int\sum_l p_l\big(r^k_{jl}+\beta v_l\big)\,d\alpha(p),$$
--   the supremum over probability vectors $\tau$ on the decisions in state $j$ and the infimum over probability measures $\alpha$ carried by $S_j^k$. Then
--
--   1. the equations $v_j=(Tv)_j$, $j=1,\dots,N$, have exactly one solution; and
--   2. the max-min return $\bar v$ of criterion (2) (the maximum over pure stationary policies of nature's minimum) solves them: $\bar v_j=(T\bar v)_j$ for every $j$.
--
--   The paper writes "where … $\bar v_j$ is the max-min return of (2). The solution to (4) exists and is unique"; both parts are stated. Proposition 1 justifies the dynamic-programming equations corresponding to criterion (2).
--
--   **Formalization Note.** The printed (4) lacks the integral sign and has an unmatched brace; the integral against $\alpha$ is formalized (see the definition `Eq4`). The proof is cited from Satia's thesis and not given in the paper.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 730, Proposition 1, Eq. (4)

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Eq4

namespace SatiaLave.MaxMin

/-- Proposition 1, p. 730: the dynamic-programming equations (4), `v_j = eq4Op M v j` for every
state `j`, have exactly one solution, and the max-min return of criterion (2) solves them. -/
theorem prop1_eq4_unique_solution {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    (∃! v : S → ℝ, ∀ j, v j = eq4Op M v j) ∧ ∀ j, maxMinValue M j = eq4Op M (maxMinValue M) j := by sorry

end SatiaLave.MaxMin
