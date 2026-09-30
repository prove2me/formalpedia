-- Prove2me | Theorems.Thm_UnderstandingML_birkhoff_von_neumann
-- name    : UnderstandingML.birkhoff_von_neumann
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:54:15.829287+00:00
-- url     : https://prove2.me/theorems/f6206dcc-d384-43f9-a449-77d2b49db1bd
-- title:
--   Claim 17.3 (Birkhoff–von Neumann): the doubly stochastic matrices are the convex hull of the permutation matrices
-- statement:
--   **Claim 17.3 (Birkhoff 1946, von Neumann 1953).** The set of doubly stochastic matrices in $\mathbb{R}^{r \times r}$ is the convex hull of the set of permutation matrices in $\mathbb{R}^{r \times r}$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §17.4.1 p. 243, Claim 17.3 (Birkhoff 1946, von Neumann 1953)

import Definitions.Def_UnderstandingML_Multiclass

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Claim 17.3 (Birkhoff 1946, von Neumann 1953)** (p. 243). The set of doubly stochastic
matrices in `ℝ^{r×r}` is the convex hull of the set of permutation matrices in `ℝ^{r×r}`. -/
theorem birkhoff_von_neumann (r : ℕ) :
    doublyStochastic ℝ (Fin r) = convexHull ℝ
      {M : Matrix (Fin r) (Fin r) ℝ | ∃ σ : Equiv.Perm (Fin r), M = σ.permMatrix ℝ} := by sorry

end UnderstandingML
