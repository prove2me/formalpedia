-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_basis_projector_embedding
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.basis_projector_embedding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:35:44.444382+00:00
-- url     : https://prove2.me/theorems/75f515b7-3e2e-4bb5-a810-76c7a7eff8a0
-- title:
--   §II Eqs.(24)–(25): exponentially many equivariant phase features
-- statement:
--   Let $m\le2^n$ feature labels be injected into the computational basis of $n$ qubits by $e$. Put $E(x)=\exp[-i\sum_{k<m}x_k|e(k)\rangle\langle e(k)|]$. Extend a feature permutation $\sigma$ by identity on every unused basis label. Its permutation matrix $U_\sigma$ is unitary, obeys the group law, and satisfies $E(\sigma x)=U_\sigma E(x)U_\sigma^\dagger$. For distinct $k,l$,
--   $$U_{(kl)}=|e(k)\rangle\langle e(l)|+|e(l)\rangle\langle e(k)|+\sum_{j\ne e(k),e(l)}|j\rangle\langle j|.$$
--   All $2^n$ labels can be used. This is a capacity for phase labels, without injectivity modulo global phase or an implementation-efficiency claim.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 6, §II Eqs.(24)–(25): exponentially many equivariant phase features

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

/-- PDF pp.5–6, Eqs.(24),(25): all unused labels are fixed. Capacity counts basis labels,
not independent physical phases modulo global phase. -/
theorem basis_projector_embedding (n m : ℕ) (hm : m ≤ 2 ^ n) (e : Fin m ↪ Qubits n) :
    featureMatrix e 1 = 1 ∧
    (∀ s t, featureMatrix e (s * t) = featureMatrix e s * featureMatrix e t) ∧
    (∀ s, featureMatrix e s ∈ Matrix.unitaryGroup (Qubits n) ℂ) ∧
    (∀ s x, basisEncoding e (featurePullback s x) = conjugate (featureMatrix e s) (basisEncoding e x)) ∧
    (∀ k l : Fin m, k ≠ l → featureMatrix e (Equiv.swap k l) =
      Matrix.single (e k) (e l) 1 + Matrix.single (e l) (e k) 1 +
        ∑ j ∈ (Finset.univ : Finset (Qubits n)).filter (fun j => j ≠ e k ∧ j ≠ e l),
          Matrix.single j j 1) ∧
    (∃ f : Fin (2 ^ n) ↪ Qubits n, Function.Surjective f) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
