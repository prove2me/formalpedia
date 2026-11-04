-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_laminar_internal_independent
-- name    : QuantumMaxCutEnergy.laminar_internal_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:21:57.517326+00:00
-- url     : https://prove2.me/theorems/0da5f59a-9fb0-4096-9781-f2a4928b81e0
-- title:
--   Laminar independence: internal-edge incidence vectors of a laminar family are independent
-- statement:
--   **Laminar independence of the internal-edge incidence vectors** (the rigidity step of Edmonds' exactness).
--
--   Let $L$ be a finite family of vertex sets, pairwise *laminar* (any two are nested or disjoint — this is exactly
--   the shape the family of tight odd sets takes after uncrossing), with each member of size at least $3$. Suppose
--   real weights $c_S$ are given such that for every edge $e$
--   $$\sum_{S\in L,\ e\subseteq S} c_S \;=\; 0 .$$
--   Then $c_S=0$ for every $S\in L$.
--
--   **Proof.** Suppose some weight is nonzero and let $P\in L$ have $c_P\neq 0$ and *maximal cardinality* among the
--   members with nonzero weight. Call a member of $L$ *proper* (relative to $P$) if it is a proper subset of $P$, and
--   let $W$ be their union. Two cases:
--
--   * *some vertex $u$ of $P$ lies in no proper member.* Pick $v\in P$, $v\neq u$. Any member containing both $u$ and
--     $v$ is either $P$ itself or strictly larger than $P$ — proper members miss $u$, and members crossing $P$ cannot
--     contain two of its vertices. So the sum at the edge $\{u,v\}$ is exactly $c_P$.
--   * *every vertex of $P$ lies in some proper member.* Take a proper member $T_1\subseteq P$ of maximal cardinality,
--     and $v\in P\setminus T_1$, together with $u\in T_1$. A proper member containing both would strictly contain
--     $T_1$, contradicting maximality; a member crossing $P$ cannot contain two of its vertices; so again the sum at
--     the edge $\{u,v\}$ of $P\setminus T_1$ with a vertex of $T_1$ is exactly $c_P$.
--
--   Either way the hypothesis forces $c_P=0$, a contradiction.
--
--   **Role.** This is the linear-algebra core of the rigidity step: with a laminar family of tight odd sets, the
--   constraint rows are independent *on the support*, which is what pins the polytope point down to $\{0,1\}$-valued
--   coordinates and hence to an integral matching. The statement deliberately avoids linear algebra: independence is
--   phrased as "a vanishing weighted sum forces all weights to vanish", which is what the rigidity argument consumes.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Schrijver, Combinatorial Optimization, Ch. 25, Sec. 25.2 (independence of the rows of a laminar family of tight odd sets).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Laminar independence.** For a laminar family of sets of size at least three, the incidence vectors of
their internal edge sets are linearly independent: if a weighted sum of the indicators `1[e ⊆ S]` vanishes on
every edge, then every weight vanishes. -/
theorem laminar_internal_independent {n : ℕ} (L : Finset (Finset (Fin n)))
    (hL3 : ∀ S ∈ L, 3 ≤ S.card)
    (hlam : ∀ S ∈ L, ∀ T ∈ L, S ≠ T → S ⊆ T ∨ T ⊆ S ∨ Disjoint S T) :
    ∀ c : Finset (Fin n) → ℝ,
      (∀ e : Edge n, ∑ S ∈ L, (if e.val.1 ∈ S ∧ e.val.2 ∈ S then c S else 0) = 0) →
      ∀ S ∈ L, c S = 0 := by sorry

end QuantumMaxCutEnergy
