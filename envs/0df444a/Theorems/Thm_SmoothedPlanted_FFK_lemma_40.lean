-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_lemma_40
-- name    : SmoothedPlanted.FFK.lemma_40
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:33:54.282464+00:00
-- url     : https://prove2.me/theorems/558c84fb-88aa-49be-83f3-a33cbdd8c3b8
-- title:
--   Lemma 40 — the SDP mass of an optimal solution on V \ S is at most Θ(H_{V\S}, k, ∆) (hereditary restriction)
-- statement:
--   In the planted setting of Lemma 39 ($k\ge1$, $\Delta\ge0$, $|S|=k$, and a $\Delta$-consistent assignment), let $M$ be any optimal lifted SDP solution and let $g(i)=\sum_a M_{ia,ia}$. Then
--   $$\sum_{i\notin S}g(i)=\sum_{i\notin S}\sum_a M_{ia,ia}\le\Theta(H_{V\setminus S},k,\Delta).$$
--   The graph on the right is induced by the outside variables with the same global parameters $k,\Delta$.
--
--   Differences from the source:
--   - encoding: finite variables and alphabet → variables and alphabet indexed by Fin n and Fin q; unordered pairs represented by i < j; reason: finite relabelling is bijective and counts every pair once
--   - generalization: labels y of a fixed CSP type, with symmetric relations R_y → all symmetric Boolean relations are available as labels; reason: pushforward along y ↦ R_y preserves every constraint and violation probability; each original type is a subclass
--   - encoding: unit u and vectors w in arbitrary finite dimension → positive semidefinite Gram matrix indexed by Option of the vertex type (literals in the lifted program); reason: every such vector family has this Gram matrix and each PSD matrix has a finite-dimensional realization; none is u
--   - encoding: sum over unordered edges and ordered distinct literal pairs → one half of the adjacency sum and the full ordered distinct-pair sum; reason: symmetric Gram entries count each unordered edge twice; the bounds remain Δ and k(k−1)
--   - encoding: planted setting of Lemma 39 used in Lemmas 40 and 42 → explicit S.card = k, k ≥ 1, Δ ≥ 0 and a Δ-consistent planted assignment; reason: these are the standing hypotheses of the rounding analysis, not facts assumed from a target lemma
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Lemma 40, printed p. 26 (PDF p. 28), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Theta
import Definitions.Def_SmoothedPlanted_FFK_Incompatibility
import Definitions.Def_SmoothedPlanted_FFK_Consistent

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem lemma_40 {n q : ℕ} (Y : CSP (Fin n) q) (S : Finset (Fin n))
    (σ : S → Fin q) (k : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hk : 1 ≤ k)
    (hS : S.card = k) (hσ : Consistent Y S σ Δ)
    (M : Gram (Fin n × Fin q)) (hM : liftedOptimal (incompatibility Y) k Δ M) :
    (∑ i ∈ Sᶜ, variableMass M i) = (∑ i ∈ Sᶜ, ∑ a : Fin q, M (some (i,a)) (some (i,a))) ∧
    (∑ i ∈ Sᶜ, variableMass M i) ≤ theta (incompatibility (restrictCSP Y Sᶜ)) k Δ := by sorry

end SmoothedPlanted.FFK
