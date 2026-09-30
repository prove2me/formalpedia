-- Prove2me | Theorems.Thm_UnderstandingML_ratiocut_trace
-- name    : UnderstandingML.ratiocut_trace
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:17:49.500985+00:00
-- url     : https://prove2.me/theorems/b320d2fd-cdb0-4d6d-a616-4eb1ef5ed77f
-- title:
--   Lemma 22.3: for H_{i,j} = |C_j|^{−1/2} 𝟙[i ∈ C_j], the columns of H are orthonormal and RatioCut(C₁,…,C_k) = trace(HᵀLH)
-- statement:
--   **Lemma 22.3.** Let $C_1, \dots, C_k$ be a clustering and let $H \in \mathbb{R}^{m \times k}$ be the matrix such that $H_{i,j} = \frac1{\sqrt{|C_j|}}\mathbb{1}[i \in C_j]$. Then, the columns of $H$ are orthonormal to each other and $\operatorname{RatioCut}(C_1, \dots, C_k) = \operatorname{trace}(H^\top L H)$.
--
--   Formally: $W$ symmetric, $C$ a partition of $[m]$ into nonempty clusters; orthonormality as $H^\top H = I_k$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §22.3.2 p. 316, Lemma 22.3

import Definitions.Def_UnderstandingML_Clustering

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 22.3** (p. 316). Let `C₁, …, C_k` be a clustering and let `H ∈ ℝ^{m×k}` be the matrix
with `H_{i,j} = |Cⱼ|^{−1/2} 𝟙[i ∈ Cⱼ]`. Then the columns of `H` are orthonormal to each other and
`RatioCut(C₁, …, C_k) = trace(Hᵀ L H)`. For a symmetric `W` and a partition of `[m]` into
nonempty clusters. -/
theorem ratiocut_trace {m k : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (hW : W.IsSymm)
    (C : Fin k → Finset (Fin m)) (hC : IsPartition Finset.univ C) (hne : ∀ i, (C i).Nonempty) :
    (clusterIndicator C).transpose * clusterIndicator C = 1 ∧
      ratioCut W C = Matrix.trace ((clusterIndicator C).transpose * laplacian W * clusterIndicator C) := by sorry

end UnderstandingML
