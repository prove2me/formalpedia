-- Prove2me | Theorems.Thm_TeschlODE_SturmLiouville_compact_symmetric_exists_eigenvalue
-- name    : TeschlODE.SturmLiouville.compact_symmetric_exists_eigenvalue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:25:28.317989+00:00
-- url     : https://prove2.me/theorems/3c3ab26d-bd76-45ea-adc0-4b9d5017291b
-- title:
--   Theorem 5.5 — a compact symmetric operator has an eigenvalue with |α₀| = ‖A‖
-- statement:
--   Let $H_0$ be a nonzero complex inner product space (not necessarily complete) and $A : H_0 \to H_0$ a compact symmetric operator. Then $A$ has an eigenvalue $\alpha_0$ with
--   $$|\alpha_0| = \|A\| = \sup_{\|f\| = 1} \|A f\| . \qquad (5.39)$$
--
--   This is the step that produces eigenvalues at all: a symmetric operator in general need not have any, and compactness supplies the first one, of maximal modulus. Iterating it on orthogonal complements gives the spectral theorem (Theorem 5.6).
--
--   **Formalization Note.** The operator norm is expressed without a real supremum: $|\alpha_0|$ is the least upper bound (`IsLUB`) of $\{\|Af\| : \|f\| = 1\}$. This set is bounded because $A$ is compact, and nonempty because $H_0 \ne \{0\}$; the hypothesis `Nontrivial E` is needed since on the zero space there is no eigenvector, and the book tacitly excludes that case. Symmetry is Mathlib's `LinearMap.IsSymmetric`, which for an everywhere defined operator is (5.36).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 150, Theorem 5.5

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_IsCompactOp

namespace TeschlODE.SturmLiouville

/-- Teschl, Theorem 5.5, p. 150: a compact symmetric operator `A` on a (nonzero) complex inner
product space `H₀` has an eigenvalue `α₀` with `|α₀| = ‖A‖ = sup_{‖f‖ = 1} ‖A f‖` (5.39).
The operator norm is stated as: `|α₀|` is the least upper bound of `{‖A f‖ : ‖f‖ = 1}`. -/
theorem compact_symmetric_exists_eigenvalue {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [Nontrivial E] (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (hsym : A.IsSymmetric) :
    ∃ α₀ : ℂ, (∃ u : E, u ≠ 0 ∧ A u = α₀ • u) ∧
      IsLUB {x : ℝ | ∃ f : E, ‖f‖ = 1 ∧ x = ‖A f‖} ‖α₀‖ := by sorry

end TeschlODE.SturmLiouville
