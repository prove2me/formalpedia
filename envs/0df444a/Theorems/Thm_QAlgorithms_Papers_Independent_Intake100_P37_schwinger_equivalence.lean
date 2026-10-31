-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_schwinger_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.schwinger_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:03:53.696715+00:00
-- url     : https://prove2.me/theorems/53482713-30c0-4340-9def-c3eb74a351b4
-- title:
--   Explicit Schwinger equivalence and singlet relabeling
-- statement:
--   Fix $A,m\ge0$ and real $\gamma,t$. The normalized occupation embedding $E_0$ sends an atomic occupation $(i,j,A-i-j)$ to the positive equally weighted superposition of all words with those counts in the alphabet $(g_1,g_2,e)$, and leaves photons unchanged. Let $J_{-,a}=\sum_k|g_a^k\rangle\langle e^k|$ and $B_{-,a}=b_a^\dagger c$.
--
--   The atomic and atom-photon embeddings are isometries and intertwine the actual collective lowering operators, Hamiltonians, and propagators:
--
--   $$
--   J_{-,a}E_{\rm atoms}=E_{\rm atoms}B_{-,a},\qquad
--   H_{\rm physical}E_0=E_0H_{\rm osc},\qquad
--   e^{-itH_{\rm physical}}E_0=E_0e^{-itH_{\rm osc}}.
--   $$
--
--   In particular the purely atomic emission coefficient is $\sqrt{(i+1)(A-i-j)}$; the photon creation operator remains unapplied in (A2). Both Hamiltonians are Hermitian. The explicit ground relabeling $R:g_1\mapsto b_2,\ g_2\mapsto-b_1$ is unitary, satisfies $H_{\rm five}=RH_{\rm osc}R^\dagger$, and gives the physical intertwiner $E=E_0R^\dagger$. The physical Hamiltonian commutes with all atom permutations and its evolution from every normalized all-excited bosonic input is atom-permutation invariant. This establishes the oscillator description from individual atoms rather than assuming symmetry of arbitrary states.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 3, Sec. II B, Eqs.(9)-(15); Appendix A, Eqs.(A1)-(A2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3-4 Eqs.(9)-(15), p.9 Eqs.(A1)-(A2): Schwinger equivalence
via the actual d=3 multinomial embedding, and the fixed singlet relabeling.
The A2 coefficient is atomic only; photon stimulation is counted in H. -/
theorem schwinger_equivalence (A m : ℕ) (gamma t : ℝ) :
    (physicalH 2 A m gamma).IsHermitian ∧
    (oscH 2 A m gamma).IsHermitian ∧ (fiveH A m gamma).IsHermitian ∧
    (QAlgorithms.Papers.Independent.Support21.P16.occupationEmbedding 3 A)ᴴ * QAlgorithms.Papers.Independent.Support21.P16.occupationEmbedding 3 A = 1 ∧
    (∀ a : Fin 2,
      collectiveLower 2 A a * QAlgorithms.Papers.Independent.Support21.P16.occupationEmbedding 3 A =
        QAlgorithms.Papers.Independent.Support21.P16.occupationEmbedding 3 A * occupationLower 2 A a) ∧
    (physicalEmbedding 2 A m)ᴴ * physicalEmbedding 2 A m = 1 ∧
    physicalH 2 A m gamma * physicalEmbedding 2 A m =
      physicalEmbedding 2 A m * oscH 2 A m gamma ∧
    QAlgorithms.Papers.Independent.Claimed50.P15.propagator (physicalH 2 A m gamma) t * physicalEmbedding 2 A m =
      physicalEmbedding 2 A m * QAlgorithms.Papers.Independent.Claimed50.P15.propagator (oscH 2 A m gamma) t ∧
    groundRelabel A m ∈ Matrix.unitaryGroup (OscBasis 2 A m) ℂ ∧
    fiveH A m gamma = groundRelabel A m * oscH 2 A m gamma * (groundRelabel A m)ᴴ ∧
    physicalH 2 A m gamma * singletEmbedding A m =
      singletEmbedding A m * fiveH A m gamma ∧
    (∀ pi : Equiv.Perm (Fin A),
      physicalH 2 A m gamma * atomPermutation A m pi =
        atomPermutation A m pi * physicalH 2 A m gamma ∧
      ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
        act (atomPermutation A m pi) (physicalOutput A m gamma t psi) =
          physicalOutput A m gamma t psi) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
