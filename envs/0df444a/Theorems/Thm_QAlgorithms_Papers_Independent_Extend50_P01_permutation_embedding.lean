-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_permutation_embedding
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.permutation_embedding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:31:54.380433+00:00
-- url     : https://prove2.me/theorems/647dbf82-52b3-4c6d-9b76-0875567f8f67
-- title:
--   §II permutation symmetries, Eqs.(18)–(20): local rotation and sign equivariance
-- statement:
--   For $d$ real features, define $E(x)=\bigotimes_i e^{-ix_iZ/2}$. A signed permutation $g=(\sigma,b)$ acts by $(gx)_i=(-1)^{b_i}x_{\sigma^{-1}(i)}$. Its Hilbert-space action sends $|q\rangle$ to the basis vector with bits $q_{\sigma^{-1}(i)}\oplus b_i$. With multiplication $(\sigma,b)(\tau,c)=(\sigma\tau,b\oplus c\circ\sigma^{-1})$, these operations form a group and their matrices form an ordinary unitary representation. For every $x$ and $g$,
--   $$E(gx)=U_gE(x)U_g^\dagger.$$
--   Thus every subgroup of signed feature permutations inherits equivariance. Inverse pullback consistently implements a left action, equivalent to relabeling the printed permutation convention.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 5, §II permutation symmetries, Eqs.(18)–(20): local rotation and sign equivariance

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P01

noncomputable section

open scoped Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P01

attribute [local instance] Classical.propDecidable Classical.decEq

-- PDF pp.3,8: reuse the accepted operator type, exp(-itH), and A X A†.
-- Notation specializes the imported interfaces without introducing duplicate declarations.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "evolve" => QAlgorithms.Papers.Independent.Information100.P32.evolution

local notation "conjugate" => QAlgorithms.conjSuperop

-- PDF pp.3,10–11: the imported quadratic form is Re(psi† A psi).

local notation "expectation" => QAlgorithms.Papers.Independent.Information100.P21.quad

-- PDF pp.5,16–19: accepted active-wire operator, with identities on all spectators.

local notation "onWire" => QAlgorithms.Papers.Independent.Advance50.P49.onWire

-- PDF p.5: the imported phase-free Pauli tensor uses 0=I,1=X,2=Y,3=Z.

local notation "pauliWord" => QAlgorithms.Papers.Independent.Gap48.P33.pauliWord

/-- PDF p.5, Eqs.(18)–(20): left-action relabeling and honest signed-permutation representation. -/
theorem permutation_embedding (d : ℕ) :
    (∀ g h k : SignedPerm d, signedMul (signedMul g h) k = signedMul g (signedMul h k)) ∧
    (∀ g : SignedPerm d, signedMul (1, fun _ => false) g = g ∧
      signedMul g (1, fun _ => false) = g ∧
      signedMul (signedInv g) g = (1, fun _ => false) ∧
      signedMul g (signedInv g) = (1, fun _ => false)) ∧
    signedMatrix (1, fun _ : Fin d => false) = 1 ∧
    (∀ g h : SignedPerm d, signedMatrix (signedMul g h) = signedMatrix g * signedMatrix h) ∧
    (∀ g : SignedPerm d, signedMatrix g ∈ Matrix.unitaryGroup (Qubits d) ℂ) ∧
    (∀ (g h : SignedPerm d) (x : Fin d → ℝ),
      signedData (signedMul g h) x = signedData g (signedData h x)) ∧
    (∀ (g : SignedPerm d) (x : Fin d → ℝ),
      localEncoding pauliZ (signedData g x) = conjugate (signedMatrix g) (localEncoding pauliZ x)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
