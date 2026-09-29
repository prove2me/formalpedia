-- Prove2me | Theorems.Thm_RHLinalg_trace_mul_nonneg_of_posSemidef
-- name    : RHLinalg.trace_mul_nonneg_of_posSemidef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:38:48.66649+00:00
-- url     : https://prove2.me/theorems/6d74815a-3e51-470f-9972-f23ea023b677
-- title:
--   Trace positivity: $\operatorname{Re}\operatorname{tr}(AB) \ge 0$ for positive semidefinite $A, B$
-- statement:
--   Let $A, B$ be $n \times n$ matrices over an `RCLike` field, both positive semidefinite.
--
--   **Statement.**
--   $$0 \;\le\; \operatorname{Re} \operatorname{tr}(A B).$$
--
--   The proof diagonalizes $A = U D U^{\mathsf H}$: then $\operatorname{tr}(AB) = \operatorname{tr}\bigl((U^{\mathsf H} B U) D\bigr) = \sum_i \lambda_i \, (U^{\mathsf H} B U)_{ii}$, where each eigenvalue $\lambda_i \ge 0$ (PSD spectrum) and each diagonal entry $(U^{\mathsf H} B U)_{ii} \ge 0$ (diagonal of a positive semidefinite matrix).
--
--   In the module `Zeta23.LinAlg.RankTrace` this standard fact is consumed by the rank–trace inequality `RHLinalg.rank_trace_ineq`, where cross terms of the form $\operatorname{tr}(P\,Q_\pm)$ between a positive semidefinite matrix and the positive/negative parts of a Hermitian matrix must be discarded with the correct sign.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/RankTrace.lean#L111-L128

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef

open Matrix Finset
open scoped ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem RHLinalg.trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ RCLike.re (A * B).trace := by sorry
