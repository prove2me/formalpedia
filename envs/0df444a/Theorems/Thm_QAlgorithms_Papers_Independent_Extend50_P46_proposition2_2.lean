-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_proposition2_2
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.proposition2_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:04:44.286264+00:00
-- url     : https://prove2.me/theorems/bdb19232-aa4c-45f5-bd94-8ccb2c408c79
-- title:
--   Normalized Choi isomorphism and inverse action formulas
-- statement:
--   Let $d_{\rm in},d_{\rm out}\ge1$ and fix the computational orthonormal bases. For every complex-linear superoperator $N$, form $J(N)=(\mathrm{id}\otimes N)(|\Omega\rangle\langle\Omega|)$ with $|\Omega\rangle=d_{\rm in}^{-1/2}\sum_i|ii\rangle$. The computed map $N\mapsto J(N)$ is a complex-linear isomorphism. Its inverse satisfies $N(X)_{xy}=d_{\rm in}\sum_{i,j}X_{ij}J(N)_{(i,x),(j,y)}$. For every positive finite auxiliary dimension $a$, $(\mathrm{id}_a\otimes N)(X)_{(u,x),(v,y)}=d_{\rm in}\sum_{i,j}X_{(u,i),(v,j)}J(N)_{(i,x),(j,y)}$. The isomorphism ranges over arbitrary complex-linear superoperators. The two inverse action formulas, as phrased in the source, apply to CPTP channels and arbitrary input operators; no density assumption is imposed on those operators.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 11, Proposition 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.11, Proposition 2.2, credited to Jam72 and Cho75: the computed
normalized Choi map is a complex-linear isomorphism. Both displayed inverse
formulas on p.11 are included, for arbitrary operators and finite auxiliaries.
The standing positive input/output dimensions guard the normalization. -/
theorem proposition2_2 (din dout : ℕ) (hdin : 1 ≤ din) (hdout : 1 ≤ dout) :
    (∃ e : (Matrix (Fin din) (Fin din) ℂ →ₗ[ℂ] Matrix (Fin dout) (Fin dout) ℂ)
        ≃ₗ[ℂ] Matrix (Fin din × Fin dout) (Fin din × Fin dout) ℂ,
      ∀ N, e N = normalizedChoiMatrix N) ∧
    (∀ (N : Matrix (Fin din) (Fin din) ℂ →ₗ[ℂ] Matrix (Fin dout) (Fin dout) ℂ)
      (X : Matrix (Fin din) (Fin din) ℂ), IsChannel N →
      N X = (din : ℂ) • (Matrix.of fun x y =>
        ∑ i, ∑ j, X i j * normalizedChoiMatrix N (i,x) (j,y))) ∧
    (∀ a : ℕ, 1 ≤ a →
      ∀ (N : Matrix (Fin din) (Fin din) ℂ →ₗ[ℂ] Matrix (Fin dout) (Fin dout) ℂ)
        (X : Matrix (Fin a × Fin din) (Fin a × Fin din) ℂ), IsChannel N →
      idTensorSuperop (R := Fin a) N X = (din : ℂ) • (Matrix.of fun x y =>
        ∑ i, ∑ j, X (x.1,i) (y.1,j) * normalizedChoiMatrix N (i,x.2) (j,y.2))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
