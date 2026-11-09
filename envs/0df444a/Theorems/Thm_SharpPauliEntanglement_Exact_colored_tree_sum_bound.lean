-- Prove2me | Theorems.Thm_SharpPauliEntanglement_Exact_colored_tree_sum_bound
-- name    : SharpPauliEntanglement.Exact.colored_tree_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:55:16.38935+00:00
-- url     : https://prove2.me/theorems/7d91aa44-1ac0-4041-a50d-fb8e27e8b610
-- title:
--   Lemma 3.7 — u=t/(1−x)^b=x/(1+x)^b; bound ≤x for degree≤b, strict <x(1+x) for degree b+1
-- statement:
--   Let $G$ be any finite simple graph of degree at most $\Delta\ge2$, and let $A\subseteq G$ be any choice of red edges. Use $b=\Delta-1$, the exact $x=x_\Delta$, $t=t_\Delta$, and the weights of (2.5), (3.9). Set
--
--   $$u=\frac{t}{(1-x)^b}=\frac{x}{(1+x)^b}.$$
--
--   For every vertex $v$,
--
--   $$\sum_{\substack{\gamma\ni v\\G[\gamma]\text{ connected}}}u^{|\gamma|}w_A(\gamma)\ \begin{cases}\le x,&\deg_G(v)\le b,\\<x(1+x),&\deg_G(v)=b+1.\end{cases}$$
--
--   The second case is strict, including at $\Delta=2$. Both cases and the identity for $u$ are stated together; the result controls the deletion argument at the equality threshold.
--
--   Differences from the source:
--   - encoding: finite graph with any red/blue coloring → Fin m vertex labels and a spanning red subgraph A <= G; reason: this represents every finite graph and every edge coloring; the original Delta is retained
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), printed/PDF p. 14–15, Lemma 3.7

import Definitions.Def_SharpPauliEntanglement_Exact_GraphWeights

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Kiani, pp. 14–15, Lemma 3.7, both cases of (3.25) and the identity (3.24). -/
theorem colored_tree_sum_bound {m : ℕ} (G A : SimpleGraph (Fin m)) (hred : A ≤ G)
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdegree : DegreeBound G Δ) :
    treeActivity Δ = criticalX Δ / (1 + criticalX Δ) ^ (Δ - 1) ∧
    ∀ v : Fin m,
      (degree G v ≤ Δ - 1 →
        connectedSum G A Δ Finset.univ v (treeActivity Δ) ≤ criticalX Δ) ∧
      (degree G v = (Δ - 1) + 1 →
        connectedSum G A Δ Finset.univ v (treeActivity Δ) <
          criticalX Δ * (1 + criticalX Δ)) := by sorry

end SharpPauliEntanglement.Exact
