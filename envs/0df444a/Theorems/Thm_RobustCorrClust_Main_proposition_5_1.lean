-- Prove2me | Theorems.Thm_RobustCorrClust_Main_proposition_5_1
-- name    : RobustCorrClust.Main.proposition_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:40:39.970478+00:00
-- url     : https://prove2.me/theorems/64e20780-c30b-4a7b-8087-40579910f9b4
-- title:
--   Proposition 5.1 — on unit-diagonal matrices Ψ_H̃(X) = ½‖X − C‖²_F + 2W_H̃ − ½‖C‖²_F − n/2 − |E⁺|
-- statement:
--   Let $G$ be a complete signed graph on $n$ vertices with $|E^+|$ positive pairs, and let $C$ be the weighted adjacency matrix of a weighted graph $\tilde H$ on the same vertices (symmetric, nonnegative, zero diagonal), with total weight $W_{\tilde H}=\tfrac12\mathbf 1^\top C\mathbf 1$. For every real symmetric $X$ with $\mathrm{diag}(X)=\mathbf 1$ (in particular every $X\in E_n$),
--   $$\Psi_{\tilde H}(X)=\tfrac12\|X-C\|_F^2+2W_{\tilde H}-\tfrac12\|C\|_F^2-\tfrac n2-|E^+| .$$
--   So minimizing $\Psi_{\tilde H}$ over $E_n$ is the nearest-correlation-matrix problem for $C$.
--
--   Differences from the source:
--   - generalization: $C$ the adjacency matrix of the rescaled sparsifier $\tilde H$ of $G^+$ → $C$ any weighted graph on the vertex set; reason: the identity holds for every weighted graph, and the paper's $\tilde H$ is one.
--   - encoding: $\|X-C\|^2$ → the squared Frobenius norm; reason: the paper's norm on matrices here is Frobenius.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 23, Proposition 5.1

import Mathlib
import Definitions.Def_RobustCorrClust_Main_Sparsifier

namespace RobustCorrClust.Main

/-- Proposition 5.1 (p. 23): with `C` the weighted adjacency matrix of `H̃`, for every symmetric `X`
with unit diagonal (in particular every `X ∈ Eₙ`),
`Ψ_H̃(X) = ½‖X − C‖²_F + 2W_H̃ − ½‖C‖²_F − n/2 − |E⁺|`. -/
theorem proposition_5_1 {n : ℕ} (G : SimpleGraph (Fin n)) (C X : Matrix (Fin n) (Fin n) ℝ)
    (hC : IsWeightedGraph C) (hX : X.IsSymm) (hdiag : ∀ u, X u u = 1) :
    PsiTilde G C X = frobSq (X - C) / 2 + 2 * totalWeight C - frobSq C / 2 - (n : ℝ) / 2 -
      (numPos G : ℝ) := by sorry

end RobustCorrClust.Main
