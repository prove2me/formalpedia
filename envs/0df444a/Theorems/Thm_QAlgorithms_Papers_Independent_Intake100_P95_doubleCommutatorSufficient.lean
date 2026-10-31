-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_doubleCommutatorSufficient
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.doubleCommutatorSufficient
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:47:16.911994+00:00
-- url     : https://prove2.me/theorems/6d29b9b4-7ec3-42b4-86f7-a8318705faad
-- title:
--   A double-commutator sufficient condition
-- statement:
--   Let $n\ge1$, let $H$ be Hermitian and traceless, and let $k$ be a Hermitian local Hamiltonian, meaning a real sum of single-qubit Pauli generators. Suppose $k$ is orthogonal, for the real Hilbert–Schmidt pairing, to every Hermitian traceless operator commuting with $H$, and suppose $[k,[k,H]]=H$. Then
--
--   $$e^{-i\phi k}He^{i\phi k}=H\cos\phi-i[k,H]\sin\phi\qquad(\phi\in\mathbb R).$$
--
--   In particular $K=e^{-i\pi k}$ belongs to the local special-unitary group, satisfies $KHK^\dagger=-H$, and reverses $e^{-itH}$ for every real $t$. This is a sufficient criterion, without any additional Lie-algebra closure hypothesis.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 3, Lemma 2: double-commutator sufficient condition

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Lemma 2, PDF p.3, (9)–(12). The Hermitian k convention is the one
used in exp(-i phi k) in the proof. No su(2)-closure is assumed. -/
theorem doubleCommutatorSufficient {n : ℕ} (hn : 0 < n) (H k : Op (QAlgorithms.Qubits n))
    (hH : IsHamiltonian H) (hk : IsLocalHamiltonian k)
    (hperp : CentralizerPerp H k) (hdouble : comm k (comm k H) = H) :
    (∀ phi : ℝ, adjointConjugation (NormedSpace.exp ((-Complex.I * (phi : ℂ)) • k)) H =
      (Real.cos phi : ℂ) • H - (Complex.I * (Real.sin phi : ℂ)) • comm k H) ∧
    (∃ K : LocalSU n, localMatrix K = NormedSpace.exp ((-Complex.I * Real.pi) • k) ∧
      localAd K H = -H ∧
      ∀ t : ℝ, localAd K (evolution H t) = evolution H (-t)) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
