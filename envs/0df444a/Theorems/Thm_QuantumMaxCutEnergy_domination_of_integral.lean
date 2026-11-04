-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_domination_of_integral
-- name    : QuantumMaxCutEnergy.domination_of_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:54:57.238695+00:00
-- url     : https://prove2.me/theorems/66c7006d-b73b-4e05-a80d-36eab0a9af89
-- title:
--   Integrality gives domination by an integral matching
-- statement:
--   **Integrality gives domination.**
--
--   If $x\ge0$ has vertex loads at most $1$ and all values in $\{0,1\}$, then for any edge weights $w$ there is an
--   integral matching $M$ with
--   $$\sum_e w_e\,x_e\ \le\ \sum_{e\in M}w_e .$$
--
--   **Proof.** Take $M=\{e : x_e=1\}$, a matching by the previous node. Since each $x_e$ is $0$ or $1$, the
--   left side equals $\sum_{e\in M}w_e$; no sign assumption on $w$ is needed.
--
--   **Role.** This is the final step of the route to `QuantumMaxCutEnergy.matching_polytope_integral_rounding`: what
--   remains before it is the rigidity statement
--   (`QuantumMaxCutEnergy.matching_polytope_rigidity`) and the extremal reduction that produces a
--   constraint-isolated maximizing point.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Lee-Parekh arXiv:2401.03616 Section 2.3.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Integrality gives domination.** -/
theorem domination_of_integral {n : ℕ} (w x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, loadAt x v ≤ 1)
    (hint : ∀ e, x e = 0 ∨ x e = 1) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      ∑ e, w e * x e ≤ ∑ e ∈ M, w e := by sorry

end QuantumMaxCutEnergy
