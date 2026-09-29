-- Prove2me | Theorems.Thm_Rudin_ch10_integral_identity_simplex
-- name    : Rudin.ch10_integral_identity_simplex
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T03:22:58.180986+00:00
-- url     : https://prove2.me/theorems/27e0d74b-4230-4548-981a-fd60f56ba97e
-- title:
--   Integral of a form over the identity simplex $Q^k$
-- statement:
--   Let $\omega=\sum_{i_1,\dots,i_k}a_{i_1\cdots i_k}\,dx_{i_1}\wedge\cdots\wedge dx_{i_k}$ be a
--   $k$-form in $\mathbb{R}^k$, and let $\sigma$ be the oriented affine simplex
--   $[\mathbf 0,\mathbf e_1,\dots,\mathbf e_k]$, that is, the $k$-surface with parameter domain $Q^k$
--   given by the identity map. Then
--   $$\int_\sigma\omega=\int_{Q^k}\sum_{\pi\in S_k}\operatorname{sgn}(\pi)\,a_{\pi(1)\cdots\pi(k)}(u)\,du .$$
--
--   The reason is that the Jacobian of the identity map along an index tuple $i$ is the determinant of
--   the $0$–$1$ matrix whose $(r,s)$ entry is $1$ exactly when $i_r=s$. That matrix has two equal rows
--   unless $i$ is injective, hence a vanishing determinant; and when $i$ is a bijection it is the
--   permutation matrix of $i$, whose determinant is $\operatorname{sgn}(i)$. So of all $k^k$ index
--   tuples only the $k!$ permutations contribute, each with the sign of the permutation.
--
--   This identity is the first step in evaluating both sides of Stokes' formula on the standard simplex,
--   and it is the precise sense in which a form, integrated over a surface, is seen only through the
--   alternating parts of its coefficients.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, Definition 10.11 (equation (35)) and Theorem 10.33, pp. 253, 273-274

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- The integral of a `k`-form over the identity surface of `Qᵏ` — Rudin's oriented affine
simplex `[0, e₁, …, e_k]` — is the integral over `Qᵏ` of the alternating sum of its
coefficients. -/
theorem ch10_integral_identity_simplex (k : ℕ) (ω : KForm k k) :
    integralOverSimplex ω ⟨id⟩
      = ∫ u in stdSimplex k,
          ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ω.coeff (⇑σ) u := by sorry

end Rudin
