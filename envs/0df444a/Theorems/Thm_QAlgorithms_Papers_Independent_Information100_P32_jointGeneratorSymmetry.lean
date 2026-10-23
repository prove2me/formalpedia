-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_jointGeneratorSymmetry
-- name    : QAlgorithms.Papers.Independent.Information100.P32.jointGeneratorSymmetry
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:43:53.933052+00:00
-- url     : https://prove2.me/theorems/b36521aa-d3b9-4148-a0be-a5ae9004cd31
-- title:
--   Joint symmetry with diagonal ancillas suffices but is not necessary
-- statement:
--   Work in arbitrary finite nonempty system and ancillary Hilbert spaces with fixed orthonormal reference bases. Write $\mathcal D(X)_{ij}=\delta_{ij}X_{ii}$ for complete dephasing in the specified basis. A density matrix is positive semidefinite with trace one; a channel is completely positive and trace preserving. Population–coherence decoupling means that diagonal and zero-diagonal operator sectors are each invariant, on all operators. Let $Z_S$ be diagonal with distinct real eigenvalues, and $Z_A$ diagonal with arbitrary real eigenvalues. Let $H$ be Hermitian, $\tau>0$, and let the physical ancilla $a$ satisfy $\mathcal D_A(a)=a$. Then
--   $$[H,Z_S\otimes I_A+I_S\otimes Z_A]=0\quad\Longrightarrow\quad
--   \operatorname{Tr}_A[e^{-i\tau H}(\,\cdot\,\otimes a)e^{i\tau H}]\text{ is decoupled}.$$
--   There are two-qubit examples with a diagonal ancilla and a decoupled channel where this joint commutation condition fails. No simple-spectrum assumption on $Z_A$ is needed.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 16, Appendix A.1 Eq.(A13): joint generator symmetry with diagonal ancillas

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.16–18, Eq.(A13): diagonal ancillas and joint generator symmetry suffice;
the ancillary eigenvalues need not be simple. No converse is asserted; a witness refutes it. -/
theorem jointGeneratorSymmetry {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] [Nonempty I] [Nonempty A]
    (h : Op (I × A)) (hh : h.IsHermitian) (zS : I → ℝ) (hz : Function.Injective zS)
    (zA : A → ℝ) (a : Op A) (ha : IsDensityMatrix a) (hd : diagonal a = a)
    (tau : ℝ) (ht : 0 < tau)
    (hcomm : Commute h (Matrix.kronecker (Matrix.diagonal fun i => (zS i : ℂ)) (1 : Op A) +
      Matrix.kronecker (1 : Op I) (Matrix.diagonal fun i => (zA i : ℂ)))) :
    Decoupled (reduced (evolution h tau) a) ∧
    (∃ (g : Op (Bool × Bool)) (b : Op Bool) (t : ℝ), g.IsHermitian ∧
      IsDensityMatrix b ∧ diagonal b = b ∧ 0 < t ∧
      ¬Commute g (Matrix.kronecker pauliZ (1 : Op Bool) +
        Matrix.kronecker (1 : Op Bool) pauliZ) ∧
      Decoupled (reduced (evolution g t) b)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
