-- Prove2me | Theorems.Thm_WernerExt_TwoSided_casimir_eigenvalue
-- name    : WernerExt.TwoSided.casimir_eigenvalue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:33.554493+00:00
-- url     : https://prove2.me/theorems/906f3790-5923-4d0c-aefc-ac8016d30671
-- title:
--   Eq. (9), p. 3 — the quadratic Casimir C_n acts on the λ-isotypic component of (ℂ^d)^{⊗n} as c(λ)
-- statement:
--   Let $d\ge2$, $n\ge0$, and let $\lambda\vdash_d n$. On the subspace of $(\mathbb C^d)^{\otimes n}$ carrying the irreducible representations labelled by $\lambda$, the quadratic Casimir operator $C_n$ acts as the scalar
--   $$c(\lambda)=\sum_{i=1}^d\left[\left(\lambda_i-\frac nd\right)^2+2(d-i)\left(\lambda_i-\frac nd\right)\right],\qquad n=\sum_{i=1}^d\lambda_i,$$
--   that is, $C_nP_\lambda=c(\lambda)P_\lambda$, where $P_\lambda$ is the projector onto that subspace.
--
--   This gives the eigenvalues of $C_A$, $C_B$ and $C_{AB}$ in Eq. (5).
--
--   **Formalization Note** $P_\lambda$ is the published `QAlgorithms.Schur.isotypicProjector λ`, the central idempotent of the $\lambda$-isotypic component of $S_n$ acting on $(\mathbb C^d)^{\otimes n}$ by permuting sites; by Schur–Weyl duality this is the $U(d)$-isotypic component of $\lambda$. The rows of $\lambda$ are its first $d$ row lengths, 0-based.
--
--   Differences from the source:
--   - encoding: the eigenvalue of the Casimir on the SU(d) irreducible subspaces labelled by λ ⊢_d n → C_n · P_λ = c(λ) · P_λ with P_λ the S_n-isotypic projector of λ (published isotypicProjector); reason: Schur–Weyl duality: the S_n-isotypic component of λ is the U(d)-isotypic component of λ
--   - encoding: 1-based rows λ_1, …, λ_d and sites → 0-based `Fin d` rows and `Fin n` sites; reason: Lean indexing convention; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, p. 3, Eq. (9); p. 2, *Solving the ground state problem* (labelling by λ ⊢_d n)

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition

namespace WernerExt.TwoSided

open Matrix
open scoped Kronecker ComplexOrder

/-- Eq. (9), p. 3: on the `λ`-isotypic component of `(ℂ^d)^{⊗ n}` the quadratic Casimir
`C_n` acts as the scalar `c(λ) = ∑_i [(λ_i − n/d)² + 2(d − i)(λ_i − n/d)]`. -/
theorem casimir_eigenvalue (d n : ℕ) (hd : 2 ≤ d) (lam : QAlgorithms.Schur.Partition d n) :
    casimirOn d n * QAlgorithms.Schur.isotypicProjector lam =
      ((casimirValue (fun i : Fin d => lam.val.rowLen i) : ℝ) : ℂ) •
        QAlgorithms.Schur.isotypicProjector lam := by sorry

end WernerExt.TwoSided
