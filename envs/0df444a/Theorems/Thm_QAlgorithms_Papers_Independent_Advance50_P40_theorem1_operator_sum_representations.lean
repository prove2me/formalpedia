-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P40_theorem1_operator_sum_representations
-- name    : QAlgorithms.Papers.Independent.Advance50.P40.theorem1_operator_sum_representations
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:00:40.437165+00:00
-- url     : https://prove2.me/theorems/87a1628e-266b-4440-b98b-1194460179f5
-- title:
--   Theorem 1: general and Hermitian operator-sum representations (rectangular typing corrected)
-- statement:
--   Let $n,m\geq1$ and $\Phi:M_n(\mathbb C)\to M_m(\mathbb C)$ be an arbitrary function. Then $\Phi$ is complex-linear if and only if there are a finite index set and two families $E_a,E'_a\in\mathbb C^{m\times n}$ such that, on every matrix $X$,
--   $$\Phi(X)=\sum_a E_a X(E'_a)^\dagger.$$
--   Within the class of complex-linear maps, $\Phi$ preserves Hermiticity if and only if there are finitely many $E_a\in\mathbb C^{m\times n}$ and real coefficients $c_a$ such that, on every matrix $X$,
--   $$\Phi(X)=\sum_a c_a E_a X E_a^\dagger.$$
--   No positivity of $c_a$ or trace-preservation condition is imposed; an empty sum represents the zero map. Lean expresses complex linearity by agreement everywhere with a bundled complex-linear map.
--
--   **Source correction.** The printed first clause assigns $E'_a$ size $n\times m$ while taking its adjoint. Change only this size to $m\times n$, which is forced by the displayed matrix product; retain arbitrary positive $n,m$ and both clauses.
-- source:
--   Vanishing quantum discord is necessary and sufficient for completely positive maps, arXiv:0808.0175v2, PDF p. 1, Theorem 1, Eqs.(2)–(3)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

/-- Theorem 1, PDF p. 1, Eqs. (2)-(3), with a minimal rectangular typing correction.
Printed: E and Eprime have sizes m by n and n by m in E X Eprime-dagger.
Changed: both operation-element families have size m by n; the adjoint is retained.
Why: E X has size m by n, so Eprime-dagger must have size n by m.
Linearity means equality on every matrix with a complex-linear map. The signed
Hermitian representation is asserted within that class, as in the source's
"Linear maps" paragraph. Coefficients are arbitrary reals, not necessarily positive.
Finite sums may be empty, representing the zero map. No trace condition is added. -/
theorem theorem1_operator_sum_representations {n m : ℕ} [NeZero n] [NeZero m]
    (Phi : SystemMatrix n → SystemMatrix m) :
    ((∃ L : SystemMatrix n →ₗ[ℂ] SystemMatrix m, ∀ X, L X = Phi X) ↔
      ∃ (r : ℕ) (E Eright : Fin r → Matrix (Fin m) (Fin n) ℂ),
        ∀ X, Phi X = ∑ a, E a * X * (Eright a).conjTranspose) ∧
    ((∃ L : SystemMatrix n →ₗ[ℂ] SystemMatrix m, ∀ X, L X = Phi X) →
      ((∀ X, X.IsHermitian → (Phi X).IsHermitian) ↔
        ∃ (r : ℕ) (c : Fin r → ℝ) (E : Fin r → Matrix (Fin m) (Fin n) ℂ),
          ∀ X, Phi X = ∑ a, (c a : ℂ) • (E a * X * (E a).conjTranspose))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P40

end
