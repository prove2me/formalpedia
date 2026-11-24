-- Prove2me | Theorems.Thm_SensitivityGraphPopulation_integral_independence_bound
-- name    : SensitivityGraphPopulation.integral_independence_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:13.313964+00:00
-- url     : https://prove2.me/theorems/eb5984e2-fe49-4768-a6c6-5c5525af998a
-- title:
--   Integral edge bound from an independence cap
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices, and let $\alpha>0$ be an integer bounding the size of every independent set. Write $n=\alpha q+r$ with $0\le r<\alpha$, and define
--
--   $$E(n,\alpha)=\alpha\binom q2+rq.$$
--
--   Then $E(n,\alpha)\le e(G)$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/IntegralGraphPopulation.lean lines 53–70; SHA256 9d86c4eb9053c08d7ec4547f7f2bf448c9e34dc489207e5d5db311e45b93c7ee; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_GraphPopulationBounds
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_IntegralGraphPopulation
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SensitivityGraphPopulation
end SensitivityGraphPopulation
namespace SimpleGraph
end SimpleGraph


/-! The exact integral Turán lower edge count used by the source population tables. -/
open SensitivityGraphPopulation
open scoped Classical
open SimpleGraph
set_option autoImplicit false

theorem SensitivityGraphPopulation.integral_independence_bound {V : Type} [Fintype V]
    (G : SimpleGraph V) (alpha : ℕ) (hpos : 0 < alpha)
    (hind : ∀ vertices : Finset V, G.IsIndepSet vertices → vertices.card ≤ alpha) :
    minimumEdges (Fintype.card V) alpha ≤ edgeCount G := by sorry
