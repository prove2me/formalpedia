-- Prove2me | Theorems.Thm_UnderstandingML_pca_reduction_lemma
-- name    : UnderstandingML.pca_reduction_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:19:12.157522+00:00
-- url     : https://prove2.me/theorems/f3fbaff1-160b-45af-b52c-502d71375755
-- title:
--   Lemma 23.1 (as proved): for every (U, W) there is V with VᵀV = I such that (V, Vᵀ) has PCA objective ≤ that of (U, W)
-- statement:
--   **Lemma 23.1.** Let $(U, W)$ be a solution to Equation (23.1). Then the columns of $U$ are orthonormal ($U^\top U = I_n$) and $W = U^\top$.
--
--   As the proof establishes it: for every $U \in \mathbb{R}^{d \times n}$, $W \in \mathbb{R}^{n \times d}$ there is $V \in \mathbb{R}^{d \times n}$ with $V^\top V = I$ and $\sum_i\|x_i - VV^\top x_i\|^2 \le \sum_i\|x_i - UWx_i\|^2$, so (23.1) may be restricted to $U^\top U = I$, $W = U^\top$ (23.2). The literal statement is not what the proof gives ($(cU, W/c)$ has the same objective as $(U, W)$). $n \le d$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §23.1 p. 324, Lemma 23.1 with its proof, and Equation (23.2)

import Definitions.Def_UnderstandingML_DimReduction

open MeasureTheory ProbabilityTheory

namespace UnderstandingML

/-- **Lemma 23.1** (p. 324), as its proof establishes it: for every `U ∈ ℝ^{d×n}` and
`W ∈ ℝ^{n×d}` there is a `V ∈ ℝ^{d×n}` with orthonormal columns (`VᵀV = I`) such that `(V, Vᵀ)`
does not increase the objective (23.1): `∑ᵢ ‖xᵢ − VVᵀxᵢ‖² ≤ ∑ᵢ ‖xᵢ − UWxᵢ‖²`. Hence (23.1) may
be restricted to `U` with orthonormal columns and `W = Uᵀ` (23.2). The book states the lemma as
a property of every solution `(U, W)`, which is not what the proof gives, since `(cU, W/c)` has
the same objective; `n ≤ d`. -/
theorem pca_reduction_lemma {m d n : ℕ} (hn : n ≤ d) (x : Fin m → Fin d → ℝ)
    (U : Matrix (Fin d) (Fin n) ℝ) (W : Matrix (Fin n) (Fin d) ℝ) :
    ∃ V : Matrix (Fin d) (Fin n) ℝ, V.transpose * V = 1 ∧
      pcaObjective x V V.transpose ≤ pcaObjective x U W := by sorry

end UnderstandingML
