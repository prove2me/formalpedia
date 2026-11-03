-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_padWeight_mem_doublyStochastic
-- name    : QuantumMaxCutEnergy.padWeight_mem_doublyStochastic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T02:17:51.377646+00:00
-- url     : https://prove2.me/theorems/d0b4d4a7-ecea-46c2-8581-af1d4c784ca0
-- title:
--   A load-polytope point pads to a doubly stochastic matrix
-- statement:
--   **The padding of a point of the load polytope is doubly stochastic.**
--
--   For an edge weight $x\ge0$ on a graph on $n$ vertices with vertex loads at most $1$, the matrix
--   $$(\mathrm{padWeight}\,x)_{ab}=\begin{cases}1-\mathrm{load}_x(a), & a=b,\\ x_{\{a,b\}}, & a\ne b\end{cases}$$
--   has nonnegative entries and every row and column sums to $1$; i.e. it is doubly stochastic.
--
--   **Proof.** Each row is the deficit $1-\mathrm{load}_x(a)$ plus the incident edges, and the sum of the pair weights
--   over the other endpoint is exactly the load
--   (`QuantumMaxCutEnergy.loadAt_eq_sum_pairWeight`), so the row sums to $1$. The matrix is symmetric
--   ($x_{\{a,b\}}=x_{\{b,a\}}$), so the column sums agree. Nonnegativity is the hypothesis `load ≤ 1` on the
--   diagonal and `x ≥ 0` off it.
--
--   **Role.** This is where a *fractional matching* turns into a doubly stochastic matrix, so that Birkhoff's
--   theorem can be applied. In the bipartite case of Edmonds' exactness every off-diagonal entry joins the two
--   colour classes, and the decomposition into permutation matrices then yields an integral matching of at least the
--   same weight.
-- source:
--   Birkhoff-von Neumann; Edmonds, J. Res. Nat. Bur. Standards 69B (1965); the padding is the standard reduction of a fractional matching to a doubly stochastic matrix.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

theorem padWeight_mem_doublyStochastic {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, loadAt x v ≤ 1) :
    padWeight x ∈ doublyStochastic ℝ (Fin n) := by sorry

end QuantumMaxCutEnergy
