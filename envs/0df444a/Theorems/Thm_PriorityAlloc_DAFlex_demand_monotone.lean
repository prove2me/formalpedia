-- Prove2me | Theorems.Thm_PriorityAlloc_DAFlex_demand_monotone
-- name    : PriorityAlloc.DAFlex.demand_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:12.902374+00:00
-- url     : https://prove2.me/theorems/3f8ceef4-8829-497d-89b6-2d332b52788f
-- title:
--   App. A.2, p. 34 — the DA demand D_j(z) is weakly decreasing in z_j and weakly increasing in z_k, k ≠ j
-- statement:
--   Let $M$ be a market satisfying the standing assumptions and let $G_t$ be probability distributions of priorities. For the DA demand $D_j(z)$ of (A.2):
--
--   1. raising the cutoff of item $j$ weakly lowers its demand: if $w \le w'$, then $D_j(z^{j \leftarrow w'}) \le D_j(z^{j \leftarrow w})$;
--   2. raising the cutoff of another item $k \ne j$ weakly raises the demand for $j$: if $w \le w'$, then $D_j(z^{k \leftarrow w}) \le D_j(z^{k \leftarrow w'})$.
--
--   Here $z^{k \leftarrow w}$ is $z$ with its $k$-th component replaced by $w$.
--
--   This monotonicity is what makes the DA operator of Algorithm 2 monotone, and hence what gives the DA cutoff its existence via Knaster–Tarski.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), p. 34, App. A.2, 'Note that D_j(z) is weakly decreasing in z_j and weakly increasing in all other components'

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

/-- App. A.2, p. 34: `D_j(z)` is weakly decreasing in `z_j` and weakly increasing in every other
component `z_k`, `k ≠ j`. -/
theorem demand_monotone (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) :
    (∀ (z : Fin n → ℝ) (j : Fin n) (w w' : ℝ), w ≤ w' →
        demand M G (Function.update z j w') j ≤ demand M G (Function.update z j w) j) ∧
      (∀ (z : Fin n → ℝ) (j k : Fin n) (w w' : ℝ), k ≠ j → w ≤ w' →
        demand M G (Function.update z k w) j ≤ demand M G (Function.update z k w') j) := by sorry

end PriorityAlloc.DAFlex
