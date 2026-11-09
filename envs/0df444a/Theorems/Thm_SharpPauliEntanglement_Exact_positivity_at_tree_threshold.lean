-- Prove2me | Theorems.Thm_SharpPauliEntanglement_Exact_positivity_at_tree_threshold
-- name    : SharpPauliEntanglement.Exact.positivity_at_tree_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:32.843644+00:00
-- url     : https://prove2.me/theorems/91364558-3194-4b47-b670-df05982e48a7
-- title:
--   Proposition 3.8 — QG,A(s)>0 for all s∈[0,tΔ], arbitrary A⊆G, including induced graphs at the same parameters
-- statement:
--   Let $G$ be a finite simple graph of maximum degree at most $\Delta\ge2$, and let $A\subseteq G$ be any spanning subgraph. Use $\alpha,\eta$ from the original $\Delta$. For every vertex subset $S$ and every real $s$ with $0\le s\le t_\Delta$,
--
--   $$Q_{G[S],A[S]}(s)=\sum_{U\subseteq S}(-1)^{|\mathcal C(G[U])|}s^{|U|}w_A(U)>0.$$
--
--   This includes the whole graph and every induced subgraph with unchanged parameters, even if its actual maximum degree is smaller. Positivity is strict on the closed interval, including zero and the exact tree threshold, and supplies all coefficients needed for separability.
--
--   Differences from the source:
--   - encoding: the full-graph polynomial and its induced-subgraph clause → one universal formula over every finite vertex subset S; reason: components and red weights on U depend only on the induced graphs; S = V recovers the first clause without changing parameters
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), printed/PDF p. 16, Proposition 3.8

import Definitions.Def_SharpPauliEntanglement_Exact_GraphWeights

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Kiani, p. 16, Proposition 3.8. The same original Δ is used on every induced graph. -/
theorem positivity_at_tree_threshold {m : ℕ} (G A : SimpleGraph (Fin m)) (hred : A ≤ G)
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdegree : DegreeBound G Δ) :
    ∀ S : Finset (Fin m), ∀ s : ℝ, 0 ≤ s → s ≤ criticalT Δ →
      0 < weightedPolynomial G A Δ S s := by sorry

end SharpPauliEntanglement.Exact
