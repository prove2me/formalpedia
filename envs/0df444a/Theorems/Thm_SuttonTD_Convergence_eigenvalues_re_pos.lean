-- Prove2me | Theorems.Thm_SuttonTD_Convergence_eigenvalues_re_pos
-- name    : SuttonTD.Convergence.eigenvalues_re_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:52.386181+00:00
-- url     : https://prove2.me/theorems/223b05ea-e3f0-4426-8909-67788d1d7678
-- title:
--   Eigenvalues of $X^\top X D(I-Q)$ have positive real parts (§4.1, p. 28)
-- statement:
--   Let $X$ be a real $K\times N$ matrix with linearly independent columns and let $M$ be an $N\times N$ real matrix that is positive definite in the paper's sense ($y^\top My>0$ for real $y\ne0$); the paper takes $M=D(I-Q)$. Then every complex eigenvalue $\lambda$ of $X^\top X M$ satisfies
--
--   $$\operatorname{Re}\lambda>0 .$$
--
--   That is, if $v\in\mathbb C^N$, $v\ne0$ and $X^\top XMv=\lambda v$, then $\operatorname{Re}\lambda>0$. Combined with a small step size, this places the eigenvalues of $I-\alpha X^\top XD(I-Q)$ inside the unit disc.
--
--   **Formalization Note** The paper also asserts that the set of eigenvalues is "full"; that claim is not stated (it is not needed downstream).
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, p. 28 (PDF p. 20)

import Definitions.Def_SuttonTD_Convergence_IsPosDefReal
open Matrix

namespace SuttonTD.Convergence

/-- **The eigenvalues of `XᵀX D(I − Q)` have positive real parts** (Sutton 1988, §4.1, p. 28,
PDF p. 20), stated for any matrix `M` that is positive definite in the paper's sense (the paper's
`M = D(I − Q)`): if `X` has linearly independent columns and `M` is positive definite, then every
complex eigenvalue `λ` of `XᵀX M` satisfies `Re λ > 0`.

Formalization Note: an eigenvalue is a `λ ∈ ℂ` with a nonzero `v ∈ ℂ^N` such that
`(XᵀXM) v = λ v`, the matrix being viewed over `ℂ`. The paper's additional claim that the set of
eigenvalues is "full" is not part of the statement (it is not needed downstream). -/
theorem eigenvalues_re_pos {N : Type*} [Fintype N] [DecidableEq N] {K : ℕ}
    (X : Matrix (Fin K) N ℝ) (hX : LinearIndependent ℝ (fun i : N => fun k : Fin K => X k i))
    (M : Matrix N N ℝ) (hM : IsPosDefReal M) (lam : ℂ) (v : N → ℂ) (hv : v ≠ 0)
    (hev : (Xᵀ * X * M).map (algebraMap ℝ ℂ) *ᵥ v = lam • v) :
    0 < lam.re := by sorry

end SuttonTD.Convergence
