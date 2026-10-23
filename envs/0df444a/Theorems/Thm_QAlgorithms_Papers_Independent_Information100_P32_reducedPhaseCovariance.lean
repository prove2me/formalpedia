-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_reducedPhaseCovariance
-- name    : QAlgorithms.Papers.Independent.Information100.P32.reducedPhaseCovariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:44:25.909196+00:00
-- url     : https://prove2.me/theorems/4722bb39-d415-4332-815c-e42cd098ee85
-- title:
--   Joint unitary symmetry induces reduced phase covariance
-- statement:
--   Work in arbitrary finite nonempty system and ancillary Hilbert spaces with fixed orthonormal reference bases. Write $\mathcal D(X)_{ij}=\delta_{ij}X_{ii}$ for complete dephasing in the specified basis. A density matrix is positive semidefinite with trace one; a channel is completely positive and trace preserving. Population–coherence decoupling means that diagonal and zero-diagonal operator sectors are each invariant, on all operators. Let $Z_S,Z_A$ be diagonal real reference generators and $V_B(\phi)=e^{-i\phi Z_B}$. Let $U$ be unitary and $a$ a physical ancilla. Assume $[U,V_S(\phi)\otimes V_A(\phi)]=0$ and $V_A(\phi)aV_A(\phi)^\dagger=a$ for all real $\phi$. Then for all $X,\phi$,
--   $$\Phi(V_S(\phi)XV_S(\phi)^\dagger)=V_S(\phi)\Phi(X)V_S(\phi)^\dagger,$$
--   where $\Phi(X)=\operatorname{Tr}_A[U(X\otimes a)U^\dagger]$. Also $[a,Z_A]=0$; if $Z_A$ has distinct eigenvalues, $a$ is diagonal. If $Z_S$ has distinct eigenvalues, $\Phi$ is decoupled. The hypothesis is actual unitary symmetry, not the false fixed-time equivalence with Hamiltonian symmetry.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 17, Appendix A.2 Eqs.(A14)–(A23): phase covariance of reduced channel

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.16–17, Eqs.(A14)–(A23): actual joint-unitary symmetry and invariant
ancillas imply phase covariance. Simple system spectrum then implies full dephasing covariance. -/
theorem reducedPhaseCovariance {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] [Nonempty I] [Nonempty A]
    (u : Op (I × A)) (hu : u.conjTranspose * u = 1 ∧ u * u.conjTranspose = 1)
    (zS : I → ℝ) (zA : A → ℝ) (a : Op A) (ha : IsDensityMatrix a)
    (hsym : ∀ phi : ℝ, Commute u (Matrix.kronecker
      (evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi) (evolution (Matrix.diagonal fun i => (zA i : ℂ)) phi)))
    (hinv : ∀ phi : ℝ, evolution (Matrix.diagonal fun i => (zA i : ℂ)) phi * a *
      (evolution (Matrix.diagonal fun i => (zA i : ℂ)) phi).conjTranspose = a) :
    (∀ (phi : ℝ) (x : Op I),
      reduced u a (evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi * x *
        (evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi).conjTranspose) =
      evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi * reduced u a x *
        (evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi).conjTranspose) ∧
    Commute a (Matrix.diagonal fun i => (zA i : ℂ)) ∧
    (Function.Injective zA → diagonal a = a) ∧
    (Function.Injective zS → Decoupled (reduced u a)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
