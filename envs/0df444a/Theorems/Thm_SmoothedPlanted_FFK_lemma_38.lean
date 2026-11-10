-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_lemma_38
-- name    : SmoothedPlanted.FFK.lemma_38
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:33:42.447189+00:00
-- url     : https://prove2.me/theorems/6d5fd902-6f58-4027-8845-607aa1109453
-- title:
--   Lemma 38 — every feasible solution of the Robust Lifted Theta SDP has total mass ⩽ k (false at k = 0: finding I4)
-- statement:
--   For any pairwise CSP instance, natural number $k$ and real $\Delta\ge0$, every feasible solution of the Robust Lifted Theta SDP satisfies
--   $$\sum_{i,a}\|w_{i,a}\|^2\le k.$$
--   This is stated as printed, including $k=0$. It is false at that boundary; insight I4 gives a feasible solution of mass one. No $k\ge1$ hypothesis has been inserted.
--
--   Differences from the source:
--   - encoding: finite variables and alphabet → variables and alphabet indexed by Fin n and Fin q; unordered pairs represented by i < j; reason: finite relabelling is bijective and counts every pair once
--   - generalization: labels y of a fixed CSP type, with symmetric relations R_y → all symmetric Boolean relations are available as labels; reason: pushforward along y ↦ R_y preserves every constraint and violation probability; each original type is a subclass
--   - encoding: unit u and vectors w in arbitrary finite dimension → positive semidefinite Gram matrix indexed by Option of the vertex type (literals in the lifted program); reason: every such vector family has this Gram matrix and each PSD matrix has a finite-dimensional realization; none is u
--   - encoding: sum over unordered edges and ordered distinct literal pairs → one half of the adjacency sum and the full ordered distinct-pair sum; reason: symmetric Gram entries count each unordered edge twice; the bounds remain Δ and k(k−1)
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Lemma 38, printed p. 25 (PDF p. 27), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Theta
import Definitions.Def_SmoothedPlanted_FFK_Incompatibility

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem lemma_38 {n q : ℕ} (Y : CSP (Fin n) q) (k : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (M : Gram (Fin n × Fin q)) (hM : liftedFeasible (incompatibility Y) k Δ M) :
    mass M ≤ (k : ℝ) := by sorry

end SmoothedPlanted.FFK
