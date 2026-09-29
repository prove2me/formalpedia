-- Prove2me | Theorems.Thm_RHLinalg_re_trace_mul_eq_eigenvalue_bilinear
-- name    : RHLinalg.re_trace_mul_eq_eigenvalue_bilinear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:39:20.567683+00:00
-- url     : https://prove2.me/theorems/4f2c1e76-804c-44f2-a2e3-1d5ce5c5b3bc
-- title:
--   $\operatorname{Re}\operatorname{tr}(AB)$ as an eigenvalue bilinear form through $\|W_{kl}\|^2$
-- statement:
--   Let $A, B$ be $n \times n$ Hermitian matrices over an `RCLike` field, with spectral decompositions $A = U_A \operatorname{diag}(\lambda(A)) U_A^{\mathsf H}$ and $B = U_B \operatorname{diag}(\lambda(B)) U_B^{\mathsf H}$, and set $W = U_A^{\mathsf H} U_B$ (a unitary matrix). Here $\lambda_k(A)$, $\lambda_l(B)$ denote the (unsorted, Mathlib-indexed) eigenvalues `eigenvalues`, and $\|W_{kl}\|^2$ are the entries of the entrywise squared-norm matrix `normSqMatrix W`.
--
--   **Statement.**
--   $$\operatorname{Re} \operatorname{tr}(A B) \;=\; \sum_{k}\sum_{l} \lambda_k(A)\; \|W_{kl}\|^2\; \lambda_l(B).$$
--
--   That is, the real trace pairing of two Hermitian matrices is a bilinear form in their eigenvalue vectors, weighted by the doubly stochastic matrix $(\|W_{kl}\|^2)$. In the module `Zeta23.LinAlg.VonNeumann` this identity is the algebraic half of the proof of von Neumann's trace inequality `RHLinalg.vonNeumann_trace_ineq`: combining it with `RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary` and the rearrangement step over doubly stochastic matrices yields the bound by the sorted eigenvalue pairing.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/VonNeumann.lean#L76-L126

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_VonNeumann

open Matrix Finset
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem RHLinalg.re_trace_mul_eq_eigenvalue_bilinear {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace =
      ∑ k, ∑ l, hA.eigenvalues k *
        normSqMatrix (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
          (hB.eigenvectorUnitary : Matrix n n 𝕜)) k l * hB.eigenvalues l := by sorry
