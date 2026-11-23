-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_sparse_prune_trace_correct
-- name    : SparsestCutOracle.Main.sparse_prune_trace_correct
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:59:49.10402+00:00
-- url     : https://prove2.me/theorems/1dce9687-3a66-48e7-9b26-41c280960b91
-- title:
--   Theorem 8 (trace correctness) — SparsePrune guarantees for the two fair cuts
-- statement:
--   Theorem 8, pp. 37–38, restricted to its universal graph-theoretic content. Let $\psi\ge0$, let $G$ be $1$-expanding with respect to $\psi$, and write $W=\operatorname{cap}(F)$ and $H=G\setminus F$. Assume $96W\le\|\psi\|_1$. If $U,f_1$ and $P,f_2$ are precisely the two fair-pair calls in `SparsePruneTrace`, then `Pruned` holds: $\psi(P)\le48W$; at least half the $\psi$-weight survives; $H[V\setminus P]$ is $(72^{-1})$-expanding; some surviving vertex has all its neighbors surviving; and $\operatorname{cap}_H(P,V\setminus P)\le\psi(P\cap U)/12$. The deleted-edge positions in $F$ and all four conclusions are exactly those of the parent Theorem 8.
-- source:
--   Theorem 8, pp. 37–38 in STOC 2027 submission #1170; first conjunct of SparsestCutOracle.Main.sparse_prune, with the identical hypotheses on SparsePruneTrace and conclusion Pruned.

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Pruning

/-- Theorem 8, pp.37--38: graph-theoretic correctness of the two-call trace. -/
theorem SparsestCutOracle.Main.sparse_prune_trace_correct :
    ∀ (n : ℕ) (G : Graph n) (ψ : Fin n → ℝ) (F : Finset (Fin G.length))
       (U P : Finset (Fin n)) (f₁ f₂ : Flow n),
    G.NoLoops → (∀ v, 0 ≤ ψ v) → ExpandingOn G.toWGraph ψ Finset.univ 1 →
    deletedCapacity G F ≤ totalWeight ψ / 96 →
    SparsePruneTrace G ψ F U f₁ P f₂ → Pruned G ψ F P := by sorry
