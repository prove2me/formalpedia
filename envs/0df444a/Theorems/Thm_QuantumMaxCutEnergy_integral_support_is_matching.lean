-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_integral_support_is_matching
-- name    : QuantumMaxCutEnergy.integral_support_is_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:54:59.159443+00:00
-- url     : https://prove2.me/theorems/bc6ad8ca-c315-4e65-8f53-48d4348bf344
-- title:
--   The support of an integral load-feasible edge weight is a matching
-- statement:
--   **The support of an integral load-feasible edge weight is a matching.**
--
--   Let $x\ge0$ be a weight on the edges of a graph with all vertex loads $\mathrm{load}_x(v)\le1$. If every value
--   of $x$ is $0$ or $1$, then the set $M=\{e : x_e=1\}$ consists of pairwise disjoint edges.
--
--   **Proof.** If two distinct edges $e,e'$ of $M$ shared a vertex $v$, the load at $v$ would be at least
--   $x_e+x_{e'}=2$, contradicting $\mathrm{load}_x(v)\le1$.
--
--   **Role.** Together with `QuantumMaxCutEnergy.domination_of_integral` this is the last link of Edmonds'
--   exactness: once a point of the fractional matching polytope is known to be integral, its support is an
--   integral matching and it is dominated by it.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); standard endgame of the matching-polytope exactness.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- The support of an integral edge weight whose vertex loads are at most `1` is a matching. -/
theorem integral_support_is_matching {n : ℕ} (x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, loadAt x v ≤ 1)
    (hint : ∀ e, x e = 0 ∨ x e = 1) :
    ∀ e ∈ Finset.univ.filter (fun e : Edge n => x e = 1),
      ∀ e' ∈ Finset.univ.filter (fun e : Edge n => x e = 1), e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2 := by sorry

end QuantumMaxCutEnergy
