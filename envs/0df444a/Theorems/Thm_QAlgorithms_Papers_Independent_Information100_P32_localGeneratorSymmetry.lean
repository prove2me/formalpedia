-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_localGeneratorSymmetry
-- name    : QAlgorithms.Papers.Independent.Information100.P32.localGeneratorSymmetry
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:43:20.893612+00:00
-- url     : https://prove2.me/theorems/c6640b9c-1470-4591-82b9-f132636844b8
-- title:
--   Local generator symmetry suffices but is not necessary
-- statement:
--   Work in arbitrary finite nonempty system and ancillary Hilbert spaces with fixed orthonormal reference bases. Write $\mathcal D(X)_{ij}=\delta_{ij}X_{ii}$ for complete dephasing in the specified basis. A density matrix is positive semidefinite with trace one; a channel is completely positive and trace preserving. Population–coherence decoupling means that diagonal and zero-diagonal operator sectors are each invariant, on all operators. Let $Z_S=\operatorname{diag}(z_i)$ have distinct real eigenvalues, let $H$ be a Hermitian joint Hamiltonian, $\tau>0$, and let $a$ be any physical ancilla state. For $\Phi(X)=\operatorname{Tr}_A[e^{-i\tau H}(X\otimes a)e^{i\tau H}]$,
--   $$[H,Z_S\otimes I_A]=0\quad\Longrightarrow\quad\Phi\text{ is decoupled}.$$
--   There also exist two-qubit RI models whose channel is decoupled while the displayed local commutation condition fails. The simple system spectrum is the assumption used by the source's time-average argument.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 16, Appendix A.1 Eq.(A12): local generator symmetry is sufficient

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.16,18, Eq.(A12): local Hamiltonian symmetry suffices for a simple
system reference spectrum. It is not necessary, even among RI channels. -/
theorem localGeneratorSymmetry {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] [Nonempty I] [Nonempty A]
    (h : Op (I × A)) (hh : h.IsHermitian) (z : I → ℝ) (hz : Function.Injective z)
    (a : Op A) (ha : IsDensityMatrix a) (tau : ℝ) (ht : 0 < tau)
    (hcomm : Commute h (Matrix.kronecker (Matrix.diagonal fun i => (z i : ℂ)) (1 : Op A))) :
    Decoupled (reduced (evolution h tau) a) ∧
    (∃ (g : Op (Bool × Bool)) (b : Op Bool) (t : ℝ), g.IsHermitian ∧
      IsDensityMatrix b ∧ 0 < t ∧
      ¬Commute g (Matrix.kronecker pauliZ (1 : Op Bool)) ∧
      Decoupled (reduced (evolution g t) b)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
