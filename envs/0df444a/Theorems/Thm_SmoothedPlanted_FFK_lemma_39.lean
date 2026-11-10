-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_lemma_39
-- name    : SmoothedPlanted.FFK.lemma_39
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:33:46.797552+00:00
-- url     : https://prove2.me/theorems/5d46b0cd-3622-4244-9814-b35e285ba9a9
-- title:
--   Lemma 39 — the SDP value on a planted instance is exactly k
-- statement:
--   Let $k\ge1$ be a natural number and $\Delta\ge0$. Suppose a pairwise CSP instance has a planted set $S$ of size $k$ and a $\Delta$-consistent assignment on $S$. Its incompatibility graph satisfies
--   $$\Theta(H,k,\Delta)=k.$$
--   This determines the optimal lifted SDP mass exactly.
--
--   Differences from the source:
--   - encoding: finite variables and alphabet → variables and alphabet indexed by Fin n and Fin q; unordered pairs represented by i < j; reason: finite relabelling is bijective and counts every pair once
--   - generalization: labels y of a fixed CSP type, with symmetric relations R_y → all symmetric Boolean relations are available as labels; reason: pushforward along y ↦ R_y preserves every constraint and violation probability; each original type is a subclass
--   - encoding: unit u and vectors w in arbitrary finite dimension → positive semidefinite Gram matrix indexed by Option of the vertex type (literals in the lifted program); reason: every such vector family has this Gram matrix and each PSD matrix has a finite-dimensional realization; none is u
--   - encoding: sum over unordered edges and ordered distinct literal pairs → one half of the adjacency sum and the full ordered distinct-pair sum; reason: symmetric Gram entries count each unordered edge twice; the bounds remain Δ and k(k−1)
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Lemma 39, printed p. 25 (PDF p. 27), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Theta
import Definitions.Def_SmoothedPlanted_FFK_Incompatibility
import Definitions.Def_SmoothedPlanted_FFK_Consistent

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem lemma_39 {n q : ℕ} (Y : CSP (Fin n) q) (S : Finset (Fin n))
    (σ : S → Fin q) (k : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hk : 1 ≤ k)
    (hS : S.card = k) (hσ : Consistent Y S σ Δ) :
    theta (incompatibility Y) k Δ = (k : ℝ) := by sorry

end SmoothedPlanted.FFK
