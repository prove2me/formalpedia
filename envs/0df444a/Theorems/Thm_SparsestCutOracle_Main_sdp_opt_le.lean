-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_sdp_opt_le
-- name    : SparsestCutOracle.Main.sdp_opt_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:46.765331+00:00
-- url     : https://prove2.me/theorems/c0c39899-7d1e-4058-ab06-281eddf78e54
-- title:
--   Lemma 3 — The weighted SDP lower bound
-- statement:
--   Let $G=(V,E)$ have $n\ge2$ vertices and nonnegative capacities, let $C$ be its Laplacian, and write $\Pi=\sum_{i\in V}\pi(i)$.
--
--   For strictly positive vertex weights $\pi$, let $\phi_G^*$ be the minimum weighted sparsity over nonempty proper subsets. For every $c_P\ge1$, SDP 2 has a feasible matrix $X$ satisfying
--
--   $$C\mathbin\bullet X\le2\Pi\phi_G^*.$$
--
--   In particular its optimum is at most $2\Pi\phi_G^*$. Feasibility includes positive semidefiniteness, every length-bounded path inequality, centering, and exact weighted normalization. The witness formulation retains the optimum inequality without using a possibly undefined real infimum over SDP objective values.
--
--   Differences from the source:
--   - generalization: the paper’s undirected graph → any symmetric nonnegative finite capacity function, including loops and disconnected graphs; reason: loops contribute zero to both cut capacities and the graph Laplacian; the cut-Gram witness works without connectedness, so every source graph is included
--   - encoding: OPT_SDP ≤ 2Πϕ*_G → a feasible witness X with objective at most 2Πϕ*_G, for every c_P ≥ 1; reason: the proof constructs this witness from a sparsest cut; the finite nonempty family of cut values has a minimum when n≥2 and π>0
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 18, Lemma 3

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_SDP

namespace SparsestCutOracle.Main

/-- Lemma 3, p.18: the proof's feasible witness encodes the full optimum bound. -/
theorem sdp_opt_le {n : ℕ} (hn : 2 ≤ n) (cP : ℕ) (hcP : 1 ≤ cP)
    (G : ClusterDecomp.WGraph (Fin n)) (π : Fin n → ℝ) (hπ : ∀ v, 0 < π v) :
    ∃ X : Mat n, SDPFeasible cP π X ∧
      dot (laplacian G) X ≤ 2 * totalWeight π * sparsest G π := by sorry

end SparsestCutOracle.Main
