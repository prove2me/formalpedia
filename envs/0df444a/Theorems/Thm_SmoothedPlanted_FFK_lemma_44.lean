-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_lemma_44
-- name    : SmoothedPlanted.FFK.lemma_44
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:33:52.832192+00:00
-- url     : https://prove2.me/theorems/b5753e28-3072-4e6c-a23f-e0beae839017
-- title:
--   Lemma 44 — deterministic dual-certificate bound on Θ′ from a decomposition A = B + Q + P
-- statement:
--   Let $G$ be a finite simple graph with adjacency matrix $A=B+Q+P$, where $Q$ is symmetric and $P$ is entrywise nonnegative. Suppose $\delta>0$, $\Lambda\ge0$, and $B-\delta\mathbf1\mathbf1^\top\succeq-\Lambda I$. For every natural $k$ and real $\Delta>0$,
--   $$\Theta'(G,k,\Delta)\le\frac{\Lambda+\|Q\|_{\rm op}}{\delta}+2\sqrt{\frac{2\Delta}{\delta}}.$$
--   The operator norm is the spectral norm; the displayed constant and both terms are retained.
--
--   Differences from the source:
--   - encoding: arbitrary finite graph vertices → vertices indexed by Fin n; reason: every finite graph admits such a relabelling
--   - encoding: unit u and vectors w in arbitrary finite dimension → positive semidefinite Gram matrix indexed by Option of the vertex type (literals in the lifted program); reason: every such vector family has this Gram matrix and each PSD matrix has a finite-dimensional realization; none is u
--   - encoding: sum over unordered edges and ordered distinct literal pairs → one half of the adjacency sum and the full ordered distinct-pair sum; reason: symmetric Gram entries count each unordered edge twice; the bounds remain Δ and k(k−1)
--   - encoding: B−δ11ᵀ ⪰ −ΛI → B−δ11ᵀ+ΛI is positive semidefinite; reason: algebraically identical matrix order; Matrix.PosSemidef includes symmetry of B, as the Loewner order on S^n does
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Lemma 44, printed p. 28 (PDF p. 30), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Dual
import Definitions.Def_SmoothedPlanted_FFK_Certifiable

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem lemma_44 {n : ℕ} (G : SimpleGraph (Fin n))
    (B Q P : Matrix (Fin n) (Fin n) ℝ) (δ Λ Δ : ℝ) (k : ℕ)
    (hdecomp : adjacency G = B + Q + P) (hQ : Q.IsSymm)
    (hP : ∀ i j, 0 ≤ P i j) (hδ : 0 < δ) (hΛ : 0 ≤ Λ)
    (hB : (B - Matrix.of (fun _ _ => δ) + Λ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hΔ : 0 < Δ) :
    thetaPrime G k Δ ≤ (Λ + spectralNorm Q) / δ + 2 * Real.sqrt (2 * Δ / δ) := by sorry

end SmoothedPlanted.FFK
