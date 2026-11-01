-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_hadamard_eigenphase_test
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.hadamard_eigenphase_test
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:59:27.536456+00:00
-- url     : https://prove2.me/theorems/f4483350-fd1d-40d0-a5e0-6537530a53d9
-- title:
--   §3 important example, equations (16)–(17)
-- statement:
--   Let $U$ be unitary on an invariant subspace $N$, and let $|\xi\rangle\in N$ be a normalized eigenvector with eigenvalue $\lambda=e^{2\pi i\phi}$. The circuit $\Xi(U)=H\Lambda(U)H$ preserves each eigenspace and, with its ancilla initially zero, gives
--
--   $$
--   \Xi(U)|0,\xi\rangle=\left(\frac{1+\lambda}{2}|0\rangle+\frac{1-\lambda}{2}|1\rangle\right)|\xi\rangle,
--   \quad P(0)=\frac{1+\cos(2\pi\phi)}2,\quad P(1)=\frac{1-\cos(2\pi\phi)}2.
--   $$
--
--   More generally, on that eigenspace the ancilla undergoes $H\operatorname{diag}(1,\lambda)H$ for every ancilla vector.
--
--   This records preservation as well as conditional probabilities, independently of behavior outside $N$.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 16, §3 important example, equations (16)–(17)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.16, equations (16)–(17): eigenspaces are preserved, with explicit ancilla
amplitudes and conditional Born probabilities. For a partial U, hU describes its isometric
restriction to the invariant subspace N; behavior outside N is irrelevant. -/
theorem hadamard_eigenphase_test {I : Type*} [Fintype I] [DecidableEq I]
    (N : Submodule ℂ (EuclideanSpace ℂ I)) (U : Matrix I I ℂ)
    (hU : ∃ e : N ≃ₗᵢ[ℂ] N, ∀ x : N, act U x.val = (e x).val)
    (phi : ℝ) (x : EuclideanSpace ℂ I) (hx : x ∈ N) (hnorm : IsState x)
    (heigen : act U x = Complex.exp (2 * Real.pi * phi * Complex.I) • x) :
    (∀ a : EuclideanSpace ℂ Bool,
      act (eigenphaseTest U) (tensorVec a x) = tensorVec (act (phaseAncilla phi) a) x) ∧
    act (eigenphaseTest U) (tensorVec (ket false) x) =
      tensorVec (WithLp.toLp 2 (fun b : Bool =>
        if b then (1 - Complex.exp (2 * Real.pi * phi * Complex.I)) / 2
        else (1 + Complex.exp (2 * Real.pi * phi * Complex.I)) / 2)) x ∧
    marginalFst (act (eigenphaseTest U) (tensorVec (ket false) x)) false =
      (1 + Real.cos (2 * Real.pi * phi)) / 2 ∧
    marginalFst (act (eigenphaseTest U) (tensorVec (ket false) x)) true =
      (1 - Real.cos (2 * Real.pi * phi)) / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
